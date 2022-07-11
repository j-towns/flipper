open import Prelude renaming (reverse to list-reverse')
open import Container.Traversable

open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)

open import Builtin.Reflection

open import Term
open import Util


record _<->_ (A B : Set) : Set where
  pattern
  constructor MkRev
  field
    apply   : A -> B
    unapply : B -> A
     -- unapplyApply : (a : A) -> unapply (apply a) ≡ a
     -- applyUnapply : (b : B) -> apply (unapply b) ≡ b

open _<->_ public
infix 1 _<->_

un : {A B : Set} -> (A <-> B) -> B <-> A
un (MkRev apply unapply) = MkRev unapply apply

_$|_|$_ : {A B C : Set} -> A -> (A <-> B) -> (B -> C) -> C
a $| f |$ g = g (apply f a)


private
   -- Reversible syntax
  data RevPat : Set where
    con : (c : Name)(ps : List RevPat) -> RevPat
    var : (nm : String) -> RevPat
  
  record RevEqn : Set where
    pattern
    constructor MkRevEqn
    field
      argp : RevPat
      fn : Term'
      resp : RevPat
  
  record RevBranch : Set where
    pattern
    constructor branch
    field
      inp  : RevPat
      eqns : List RevEqn
      outp : RevPat
  
  record RevTerm : Set where
    pattern
    constructor MkRT
    field
      branches : List RevBranch
  
   -- Reversal transformation
  reverse-eqn : RevEqn -> RevEqn
  reverse-eqn (MkRevEqn argp fn resp) =
    MkRevEqn resp (def (quote un) (varg fn ∷ [])) argp

  reverse-br : RevBranch -> RevBranch
  reverse-br (branch inp eqns outp) =
    branch outp (list-reverse' (fmap reverse-eqn eqns)) inp

  reverse : RevTerm -> RevTerm
  reverse (MkRT branches) = MkRT (fmap reverse-br branches)
  
   -- We use pattern matching on these 'ok' forms to lossily
   -- transform from Term to RevTerm. Any pattern that isn't ok
   -- will throw an error. We use the same ok patterns
   -- to reconstruct a Term from a RevTerm...
  pattern ok-pat-lam cs = pat-lam cs []
  pattern ok-clause tel inp term = clause tel (inp ∷ []) term
  pattern ok-cons argpat rev-fn res-tel respat rest-term =
    def (quote _$|_|$_) (
      harg _ ∷
      harg _ ∷
      harg _ ∷
      varg argpat ∷
      varg rev-fn ∷
      varg (ok-pat-lam (ok-clause res-tel respat rest-term ∷ [])) ∷ [])
  pattern reduced-cons argpat rev-fn res-tel respat rest-term =
    def (quote _$|_|$_) (
      varg argpat ∷
      varg rev-fn ∷
      varg (ok-pat-lam (ok-clause res-tel respat rest-term ∷ [])) ∷ [])

  module T-to-RT where
    private
      qc-extend : QContext -> List (String × Arg Type) -> QContext
      qc-extend = foldl \ ctx -> \ { (nm , varg _) -> ctx -, left (qone , nm)
                                   ; _             -> ctx -, right <> }

      {-# TERMINATING #-}
      Pattern-to-RevPat : QContext -> Arg Pattern -> TC RevPat
      Pattern-to-RevPat ctx (varg (var x)) = do
        left nm <- QC-index ctx x
          where right <> -> typeErrorS "Reference to hidden variable in pattern."
        return $ var nm
      Pattern-to-RevPat ctx (varg (con c ps)) = do
        ps <- traverse (Pattern-to-RevPat ctx) ps
        return $ con c ps
      Pattern-to-RevPat _ _ = typeErrorS "Patterns must either be variables or constructors"

      {-# TERMINATING #-}
      Term-to-RevPat : QContext -> Term -> TC (QContext × RevPat)
      Term-to-RevPat ctx (var x []) = do 
        ctx , nm <- QC-use ctx x
        return (ctx , var nm)
      Term-to-RevPat ctx (con c ps) = do
        ctx , ps <- args-helper ctx $ map unArg $ filter is-visible ps
        return (ctx , (con c ps))
        where
        args-helper : QContext -> List Term -> TC (QContext × List RevPat)
        args-helper ctx [] = returnTC (ctx , [])
        args-helper ctx (a ∷ args) = do
          ctx , a    <- Term-to-RevPat ctx a
          ctx , args <- args-helper    ctx args
          return (ctx , (a ∷ args)) 
      Term-to-RevPat ctx (meta m args) = blockOnMeta m
      Term-to-RevPat ctx t =
        typeError (strErr "Argument/output must be a variable or constructor" ∷ [])

      process-term : QContext -> Term -> TC (List RevEqn × RevPat)
      process-term ctx (ok-cons argpat rev-fn res-tel respat rest-term) = do
        ctx , argpat <- Term-to-RevPat ctx argpat
        rev-fn <- Term-to-Term' ctx rev-fn
        let ctx = qc-extend ctx res-tel
        respat <- Pattern-to-RevPat ctx respat
        eqns , outp <- process-term ctx rest-term
        return $ (MkRevEqn argpat rev-fn respat ∷ eqns) , outp
      process-term ctx t = do
        ctx , outp <- Term-to-RevPat ctx t
         -- TODO: Check that all variables in ctx have been used
        return $ [] , outp

      Clause-to-RevBranch : Clause -> TC RevBranch
      Clause-to-RevBranch (ok-clause tel inp term) = do
        let ctx = qc-extend [] tel
        inp <- Pattern-to-RevPat ctx inp
        eqns , outp <- process-term ctx term
        return $ branch inp eqns outp
      Clause-to-RevBranch _ = typeErrorS  "Clauses must have exactly one bound pattern."

    Term-to-RevTerm : Term -> TC RevTerm
    Term-to-RevTerm (ok-pat-lam cs) =
      fmap MkRT $ traverse Clause-to-RevBranch $ filter not-absurd cs
      where
      not-absurd = \ where
        (absurd-clause _ _) -> false
        _                   -> true
    Term-to-RevTerm (meta m args) = blockOnMeta m
    Term-to-RevTerm t = typeError (strErr "Only pattern-lambda terms can be reversed." ∷ [])

  open T-to-RT
  
  module RT-to-T where
    private
      process-tel : Context -> RevPat -> Context × List (String × Arg Type)
      process-tel ctx p = helper ctx (p ∷ [])
        where
        helper : Context -> List RevPat -> Context × List (String × Arg Type)
        helper ctx [] = ctx , []
        helper ctx (con c ps ∷ ps') =
          let ctx , tel-start = helper ctx ps
              ctx , tel-end   = helper ctx ps' in
              ctx , tel-start ++ tel-end
        helper ctx (var nm ∷ ps) =
          let ctx , tel = helper (ctx -, nm) ps in
          ctx , (nm , varg unknown) ∷ tel

      {-# TERMINATING #-}
      RevPat-to-Pattern : Context -> RevPat -> TC (Arg Pattern)
      RevPat-to-Pattern ctx (con c ps) = 
        return ∘ varg ∘ con c =<< traverse (RevPat-to-Pattern ctx) ps
      RevPat-to-Pattern ctx (var nm) =
        return ∘ varg ∘ var =<< C-lookup ctx nm

      {-# TERMINATING #-}
      RevPat-to-Term : Context -> RevPat -> TC Term
      RevPat-to-Term ctx (con c ps) =
        return ∘ con c ∘ map varg =<< traverse (RevPat-to-Term ctx) ps
      RevPat-to-Term ctx (var nm) = 
        return ∘ (\ x -> var x []) =<< C-lookup ctx nm
    
    RevTerm-to-Term : RevTerm -> TC Term
    RevTerm-to-Term (MkRT bs) =
      return ∘ ok-pat-lam =<< traverse process-branch bs
      where
      process-term : Context -> List RevEqn -> RevPat -> TC Term
      process-term ctx [] outp = RevPat-to-Term ctx outp
      process-term ctx (MkRevEqn argp fn resp ∷ eqns) outp = do
        argp <- RevPat-to-Term ctx argp
        fn <- Term'-to-Term ctx fn
        let ctx , res-tel = process-tel ctx resp
        respat <- RevPat-to-Pattern ctx resp
        rest-term <- process-term ctx eqns outp
        return (reduced-cons argp fn res-tel respat rest-term)
    
      process-branch : RevBranch -> TC Clause
      process-branch (branch inp eqns outp) = do
        let ctx , tel = process-tel [] inp
        inp <- RevPat-to-Pattern ctx inp
        term <- process-term ctx eqns outp
        return (ok-clause tel inp term)
  open RT-to-T
  
   -- Proof building
  base : {A B : Set} -> (unapply : B -> A) -> (b : B) -> unapply b ≡ unapply b
  base unapply b = refl
  
  {-
  _P|_|P_ : {A B C : Set} -> {rest : C -> A} {unapply-end : B -> A} -> (b : B)
    -> (f : B <-> C) -> ((c : C) -> rest c ≡ unapply-end (unapply f c))
    -> rest (apply f b) ≡ unapply-end b
  b P| f |P cont with apply f b | unapplyApply f b
  ... | c | refl = cont c
  -}
  
   -- To construct a proof from a reversible apply function, we replace _$|_|$_ with
   -- _P|_|P_, and the reversible pattern at the end of apply with base.
  mk-proof : (`apply `unapply : Term) -> TC Term
  mk-proof (ok-pat-lam cs) `unapply = process-branches cs
    where
    process-branches : List Clause -> TC Term
    process-branches [] = returnTC (ok-pat-lam [])
    process-branches (ok-clause tel inp term ∷ cs) = {!!}
    process-branches _ = {!!}
  mk-proof _ _ = typeError (strErr "Only pattern-lambda terms can be reversed." ∷ [])
  
  R-tactic : {A B : Set} (apply : A -> B) -> Term -> TC ⊤
  R-tactic apply hole = do
    `apply <- quoteTC apply
    apply-rt <- Term-to-RevTerm `apply
    `unapply <- RevTerm-to-Term (reverse apply-rt)

     -- bindTC (mk-proof `apply `unapply) \ `unapplyApply ->
     -- bindTC (mk-proof `unapply `apply) \ `applyUnapply ->

    unify (con (quote MkRev) (varg `apply ∷ varg `unapply ∷ [])) hole

R : {A B : Set} (apply : A -> B) {@(tactic R-tactic apply) rev : A <-> B} -> A <-> B
R apply {r} = r

-------------------------------------------------------------------------------------
-------------------------------------- TESTS ----------------------------------------
-------------------------------------------------------------------------------------

pair-swp : {A B : Set} -> A × B <-> B × A
pair-swp = R (\{ (a , b) -> b , a})

idR : {A : Set} -> A <-> A
idR = R (\ { x -> x })

test-composed : Either (Nat × Nat) Nat <-> Either Nat (Nat × Nat)
test-composed = R (
  \ { (left (m , n)) -> 
        m $| idR |$ \ { m' ->
        n $| idR |$ \ { n' ->
      right (n' , m') }}
    ; (right x) -> left x })

sum-swp : {A B : Set} -> Either A B <-> Either B A
sum-swp = R (\ { (left a) → right a
               ; (right b) → left b })

 -- Three different ways to compose two reversibles:
_+R_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> Either A B <-> Either C D
f +R g = R \ { (left a) → a $| f |$ \ { c -> left c }
             ; (right b) → b $| g |$ \ { d -> right d } }

_*R_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> A × B <-> C × D
f *R g = R \ { (a , b) -> a $| f |$ \ { c -> 
                          b $| g |$ \ { d -> (c , d) } } }

_>>>R_ : {A B C : Set} -> (A <-> B) -> (B <-> C) -> A <-> C
f >>>R g = R (
  \ { a -> a $| f |$ \ { b ->
           b $| g |$ \ { c -> c }}})

infixr 2 _>>>R_

 -- Another combinator:
uncurryR : {A B C : Set} -> (A -> B <-> C) -> A × B <-> A × C
uncurryR f = R (\ {
  (a , b) -> b $| f a |$ \ { c -> (a , c) }})

uncurryR' : {A : Set} {B C : A -> Set} -> ((a : A) -> B a <-> C a) -> Σ A B <-> Σ A C
uncurryR' f = R \ { (d , b) → b $| f d |$ \ { c -> (d , c) } }

{-
data Fin : Nat -> Set where
  z : {n : Nat} -> Fin (suc n)
  s : {n : Nat} -> Fin n -> Fin (suc n)

test-hidden-arg-in-pattern : (m : Nat) -> Fin m <-> Fin m
test-hidden-arg-in-pattern m = MkRev (\
  { z     -> z
  ; (s n) -> s n })

R≡ : {A B : Set} -> A ≡ B -> A <-> B
R≡ refl = idR
-}
{-
Nat-split : Nat <-> Nat + Nat
Nat-split = MkRev (\ { n -> {!n $| !} }) {{!!}}
  where
  part1 : Nat <-> One + One + Nat + Nat
  part1 = MkRev (\ { zero          → left <>
                   ; (suc zero)    → right (left <>)
                   ; (suc (suc n)) → n $| Nat-split |$ \ { n -> right (right n) } })

  part2 : One + One + Nat + Nat <-> Nat + Nat
  part2 = MkRev (\ { (left <>)            -> left zero
                   ; (right (left <>))      -> right zero
                   ; (right (right (left n))) -> left (suc n)
                   ; (right (right (right n))) -> right (suc n) })
-}
