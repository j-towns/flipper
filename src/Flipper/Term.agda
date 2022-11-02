module Flipper.Term where

open import Prelude hiding (abs)
open import Container.Traversable

open import Builtin.Reflection

open import Flipper.Util


data Quant : Set where
  qzero qone : Quant

data QVar : Set where
  vv : Quant -> String -> QVar  -- visible
  hv : QVar                     -- hidden, references will be replaced
                                -- by `unknown`
QContext : Set
QContext = SnocList QVar

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

QCParser : Set -> Set
QCParser = Parser QContext (List ErrorPart)

pattern errS s = right [ strErr s ]
qcpError : forall {A} -> List ErrorPart -> QCParser A
qcpError error = const (right error)

qcpSError : forall {A} -> String -> QCParser A
qcpSError error = qcpError [ strErr error ]

qcpUse : Nat -> QCParser String
qcpUse i       []                   = errS "Invalid variable lookup." -- this should be unreachable
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
QC-to-VarSet = slist-concatMap \ { (vv qzero _) → []
                                 ; (vv qone nm) → [] -, nm
                                 ; hv           → []
                                 }

module Pack (ctx : QContext) where
   -- On failure we return the name of the already-used variable which
   -- was referred to.
  Pck : Set -> Set
  Pck A = Nat -> A -> Either String A

   -- Variables which are hidden in the context need to be replaced by
   -- `unknown`, signalled by the rightmost `unit` branch here:
  pckVar : Nat -> Nat -> Either String (Either Nat ⊤)
  pckVar = go 0 ctx where
    go : Nat -> QContext -> Nat -> Nat -> Either String (Either Nat ⊤)
    go acc ctx                  (suc depth) zero    = right (left acc)
    go acc []                   zero        zero    = right (left acc)
    go acc (ctx -, vv qzero nm) zero        zero    = left nm
    go acc (ctx -, vv qone _)   zero        zero    = right (left acc)
    go acc (ctx -, hv)          zero        zero    = right (right unit)
    go acc []                   zero        (suc x) = go (suc acc) [] zero x
    go acc (ctx -, vv qzero _)  zero        (suc x) = go acc ctx zero x
    go acc (ctx -, vv qone  _)  zero        (suc x) = go (suc acc) ctx zero x
    go acc (ctx -, hv)          zero        (suc x) = go acc ctx zero x
    go acc ctx                  (suc depth) (suc x) = go (suc acc) ctx depth x

  pck        : Pck Term
  pckArgs    : Pck (List (Arg Term))
  pckArg     : Pck (Arg Term)
  pckAbs     : Pck (Abs Term)
  pckClauses : Pck (List Clause)
  pckClause  : Pck Clause
  pckSort    : Pck Sort
  pckTel     : Pck Telescope
  pckPats    : Pck (List (Arg Pattern))
  pckPatArg  : Pck (Arg Pattern)
  pckPat     : Pck Pattern

  pck d (var x args) with pckVar d x
  ... | left nm            = left nm
  ... | right (left  x)    = var x <$> pckArgs d args
  ... | right (right unit) = pure unknown
  pck d (con c args)       = con c <$> pckArgs d args
  pck d (def f args)       = def f <$> pckArgs d args
  pck d (lam v t)          = lam v <$> pckAbs d t
  pck d (pat-lam cs args)  = pat-lam <$> pckClauses d cs <*> pckArgs d args
  pck d (pi a b)           = pi <$> pckArg d a <*> pckAbs d b
  pck d (agda-sort s)      = agda-sort <$> pckSort d s
  pck d (lit l)            = pure (lit l)
  pck d (meta m args)      = meta m <$> pckArgs d args
  pck d unknown            = pure unknown

  pckArgs    d []          = pure []
  pckArgs    d (a ∷ args)  = _∷_ <$> pckArg d a <*> pckArgs d args
  pckArg     d (arg i x)   = arg i <$> pck d x
  pckAbs     d (abs s x)   = abs s <$> pck (suc d) x
  pckSort    d (set t)     = set <$> pck d t
  pckSort    d (lit n)     = pure (lit n)
  pckSort    d (prop t)    = prop <$> pck d t
  pckSort    d (propLit n) = pure (propLit n)
  pckSort    d (inf n)     = pure (inf n)
  pckSort    d unknown     = pure unknown

  pckClauses d []         = pure []
  pckClauses d (x ∷ cs)   = _∷_ <$> pckClause d x <*> pckClauses d cs

  pckClause d (clause tel ps t) = clause <$> pckTel d tel <*> pckPats d ps <*> pck (suc d) t
  pckClause d (absurd-clause tel ps) = absurd-clause <$> pckTel d tel <*> pckPats d ps

  pckTel d []                 = pure []
  pckTel d ((nm , aty) ∷ tel) = _∷_ <$> (nm ,_ <$> pckArg d aty) <*> pckTel (suc d) tel

  pckPats d []       = pure []
  pckPats d (p ∷ ps) = _∷_ <$> pckPatArg d p <*> pckPats d ps

  pckPat d (con c ps) = con c <$> pckPats d ps
  pckPat d (dot t)    = dot <$> pck d t
  pckPat d (var x)    = pure (var x)
  pckPat d (lit l)    = pure (lit l)
  pckPat d (proj f)   = pure (proj f)
  pckPat d (absurd x) = pure (absurd x)

  pckPatArg d (arg i p) = arg i <$> pckPat d p

  pack : Term -> Either String Term
  pack = pck 0
open Pack


wrapAbs : (String -> Term -> Term) -> Term -> VarSet -> Term
wrapAbs = slist-foldr

packLamWrap : Term -> QCParser Term
packLamWrap t ctx with pack ctx t
... | left nm = right (strErr ("Reference to used variable " & nm & ".") ∷ [])
... | right t =
  left (ctx , wrapAbs (\ { nm t -> lam visible (abs nm t) }) t (QC-to-VarSet ctx))

packPiWrap : Type -> QCParser Type
packPiWrap ty ctx with pack ctx ty
... | left nm  = right (strErr ("Reference to used variable " & nm & " in type.") ∷ [])
... | right ty =
  left (ctx , wrapAbs (\ { nm ty -> pi (vArg unknown) (abs nm ty) }) ty (QC-to-VarSet ctx))

patVarLookup : Nat -> QCParser String
patVarLookup v ctx with slist-index ctx v
... | just (vv qzero nm) = right (strErr ("Internal Flipper error: reference to used variable " & nm & " in pattern.") ∷ [])
... | just (vv qone  nm) = left (ctx , nm)
... | just hv = right (strErr "Reference to hidden variable in pattern." ∷ [])
... | nothing = right (strErr "Internal Flipper error: invalid de Bruijn index in pattern." ∷ [])

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
