module Flipper.Parser where

open import Prelude hiding (abs)
open import Container.Traversable

open import Builtin.Reflection

open import Flipper.SnocList


Parser : Set -> Set -> Set -> Set
Parser C E A = C -> Either (C × A) E

module _ {C E : Set} where
  instance
    FunctorParser : Functor (Parser C E)
    fmap {{FunctorParser}} f p ctx with p ctx
    ... | left (ctx , a) = left (ctx , f a)
    ... | right error = right error

    ApplicativeParser : Applicative (Parser C E)
    pure {{ApplicativeParser}} a ctx = left (ctx , a)
    _<*>_ {{ApplicativeParser}} pf pa ctx with pf ctx
    ... | right error      = right error
    ... | left (ctx , f) with pa ctx
    ...   | left (ctx , a) = left (ctx , f a)
    ...   | right error    = right error

    MonadParser : Monad (Parser C E)
    _>>=_ {{MonadParser}} pa f ctx with pa ctx
    ... | right error = right error
    ... | left (ctx , a) with f a
    ...   | pb = pb ctx

data Quant : Set where
  qzero qone : Quant

data QVar : Set where
  vv : Quant -> String -> QVar  -- visible
  hv : QVar                     -- hidden, references will be replaced
                                -- by `unknown`
QContext : Set
QContext = SnocList QVar

QCParser : Set -> Set
QCParser = Parser QContext (List ErrorPart)

pattern errS s = right [ strErr s ]
qcpError : forall {A} -> List ErrorPart -> QCParser A
qcpError error = const (right error)

qcpSError : forall {A} -> String -> QCParser A
qcpSError error = qcpError [ strErr error ]

qcpUse : Nat -> QCParser String
qcpUse i       []                   = errS "Internal Flipper error: invalid variable lookup."
qcpUse zero    (ctx -, vv qzero nm) = errS ("Attempt to re-use used variable " & nm & ".")
qcpUse zero    (ctx -, vv qone  nm) = left ((ctx -, vv qzero nm) , nm)
qcpUse zero    (ctx -, hv)          = errS "Attempt to use hidden variable."
qcpUse (suc i) (ctx -, x) with qcpUse i ctx
... | left (ctx , nm) = left ((ctx -, x) , nm)
... | right err = right err

qcpExtend : String -> QCParser ⊤
qcpExtend nm ctx = left ((ctx -, vv qone nm) , unit)

qcpHExtend : QCParser ⊤
qcpHExtend ctx = left ((ctx -, hv) , unit)

qcpCheckAllUsed : QCParser ⊤
qcpCheckAllUsed [] = left ([] , unit)
qcpCheckAllUsed (ctx -, vv qone  nm) = errS ("Unused variable " & nm & ".")
qcpCheckAllUsed (ctx -, v) with qcpCheckAllUsed ctx
... | left (ctx , unit) = left ((ctx -, v) , unit)
... | right error = right error

qcpEmpty : QCParser ⊤
qcpEmpty _ = left ([] , unit)

VarSet = SnocList String

QC-to-VarSet : QContext -> VarSet
QC-to-VarSet = slist-concatMap \ { (vv qone nm) → [] -, nm
                                 ; _            → []
                                 }

patVarLookup : Nat -> QCParser String
patVarLookup v ctx with slist-index ctx v
... | just (vv qzero nm) = errS ("Internal Flipper error: reference to used variable " & nm & " in pattern.")
... | just (vv qone  nm) = left (ctx , nm)
... | just hv = errS "Reference to hidden variable in pattern."
... | nothing = errS "Internal Flipper error: invalid de Bruijn index in pattern."

getVarSet : QCParser VarSet
getVarSet ctx = left (ctx , QC-to-VarSet ctx)


Context : Set
Context = SnocList String

CParser : Set -> Set
CParser = Parser (Context × Nat) String

cpExtend : String -> CParser ⊤
cpExtend nm (ctx , lvl) = left (((ctx -, nm) , lvl) , unit)

{-# TERMINATING #-}
cpLookup : String -> CParser Nat
cpLookup nm ([]         , lvl) = right nm
cpLookup nm ((ctx -, v) , lvl) with nm ==? v
... | true  = left (((ctx -, v) , lvl) , zero)
... | false with cpLookup nm (ctx , lvl)
...   | left ((ctx , lvl) , x) = left (((ctx -, v) , lvl) , suc x)
...   | right nm = right nm

cpRemap : VarSet -> CParser (List Nat)
cpRemap vars = go [] vars
  where
  go : List Nat -> VarSet -> CParser (List Nat)
  go done [] = pure done
  go done (vars -, nm) = do
    x <- cpLookup nm
    go (x ∷ done) vars

cpSetLevel : Nat -> CParser ⊤
cpSetLevel lvl (ctx , _) = left ((ctx , lvl) , unit)

cpUp : CParser ⊤
cpUp (ctx , lvl) = left ((ctx , suc lvl) , unit)

cpDown : CParser ⊤
cpDown (ctx , zero) = right "_"
cpDown (ctx , suc lvl) = left ((ctx , lvl) , unit)

cpGetIndex : CParser Nat
cpGetIndex (ctx , lvl) = left ((ctx , lvl) , slist-length ctx + lvl)

cpGetDepth : CParser Nat
cpGetDepth (ctx , lvl) = left ((ctx , lvl) , slist-length ctx)

cpEmpty : CParser ⊤
cpEmpty (_ , lvl) = left (([] , lvl) , unit)

cpInTC : forall {A} -> CParser A -> TC A
cpInTC cp with cp ([] , 0)
... | left (_ , a) = pure a
... | right err = typeErrorS err
