module Flipper.Core where

open import Prelude renaming (reverse to list-reverse')
  hiding (abs; flip)
open import Container.Traversable
open import Tactic.Reflection.DeBruijn

open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)

open import Builtin.Reflection

open import Flipper.Term
open import Flipper.Util


infix 1 _<->_
record _<->_ (A B : Set) : Set where
  pattern
  constructor MkF
  field
    apply   : A -> B
    unapply : B -> A
    unapplyApply : (a : A) -> unapply (apply a) ≡ a
    applyUnapply : (b : B) -> apply (unapply b) ≡ b
open _<->_ public

flip : {A B : Set} -> (A <-> B) -> B <-> A
flip (MkF apply unapply ua au) = MkF unapply apply au ua

_$|_|$_ : {A B C : Set} -> A -> (A <-> B) -> (B -> C) -> C
a $| f |$ g = g (apply f a)

private
   -- Flippable syntax
  data FPat : Set where
    con : (c : Name)(ps : List FPat) -> FPat
    var : (nm : String) -> FPat

  record FEqn : Set where
    pattern
    constructor MkFEqn
    field
      argp : FPat
      fn : Term'
      resp : FPat

  record FBranch : Set where
    pattern
    constructor branch
    field
      inp  : FPat
      eqns : List FEqn
      outp : FPat

  record FTerm : Set where
    pattern
    constructor MkRT
    field
      branches : List FBranch

   -- Reversal transformation
  reverse-eqn : FEqn -> FEqn
  reverse-eqn (MkFEqn argp fn resp) =
    MkFEqn resp (def (quote flip) (varg fn ∷ [])) argp

  reverse-br : FBranch -> FBranch
  reverse-br (branch inp eqns outp) =
    branch outp (list-reverse' (fmap reverse-eqn eqns)) inp

  reverse : FTerm -> FTerm
  reverse (MkRT branches) = MkRT (fmap reverse-br branches)

   -- We use pattern matching on these 'ok' forms to lossily
   -- transform from Term to FTerm. Any pattern that isn't ok
   -- will throw an error. We use the same ok patterns
   -- to reconstruct a Term from a FTerm...
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
      Pattern-to-FPat : QContext -> Arg Pattern -> TC FPat
      Pattern-to-FPat ctx (varg (var x)) = do
        left nm <- QC-index ctx x
          where right <> -> typeErrorS "Reference to hidden variable in pattern."
        return $ var nm
      Pattern-to-FPat ctx (varg (con c ps)) = do
        ps <- traverse (Pattern-to-FPat ctx) (filter isVisible ps)
        return $ con c ps
      Pattern-to-FPat _   (varg p) = typeError
        (strErr "Patterns must either be variables or constructors, got "
        ∷ pattErr p ∷ [])
      Pattern-to-FPat _   _        = typeErrorS "Non-visible pattern."

      {-# TERMINATING #-}
      Term-to-FPat : QContext -> Term -> TC (QContext × FPat)
      Term-to-FPat ctx (var x []) = do
        ctx , nm <- QC-use ctx x
        return (ctx , var nm)
      Term-to-FPat ctx (con c ps) = do
        ctx , ps <- args-helper ctx $ map unArg $ filter is-visible ps
        return (ctx , (con c ps))
        where
        args-helper : QContext -> List Term -> TC (QContext × List FPat)
        args-helper ctx [] = returnTC (ctx , [])
        args-helper ctx (a ∷ args) = do
          ctx , a    <- Term-to-FPat ctx a
          ctx , args <- args-helper    ctx args
          return (ctx , (a ∷ args))
      Term-to-FPat ctx (meta m args) = blockOnMeta m
      Term-to-FPat ctx t =
        typeError (strErr "Argument/output must be a variable or constructor" ∷ [])

      process-term : QContext -> Term -> TC (List FEqn × FPat)
      process-term ctx (ok-cons argpat rev-fn res-tel respat rest-term) = do
        ctx , argpat <- Term-to-FPat ctx argpat
        rev-fn <- Term-to-Term' ctx rev-fn
        let ctx = qc-extend ctx res-tel
        respat <- Pattern-to-FPat ctx respat
        eqns , outp <- process-term ctx rest-term
        return $ (MkFEqn argpat rev-fn respat ∷ eqns) , outp
      process-term ctx t = do
        ctx , outp <- Term-to-FPat ctx t
         -- TODO: Check that all variables in ctx have been used
        return $ [] , outp

      Clause-to-FBranch : Clause -> TC FBranch
      Clause-to-FBranch (ok-clause tel inp term) = do
        let ctx = qc-extend [] tel
        inp <- Pattern-to-FPat ctx inp
        eqns , outp <- process-term ctx term
        return $ branch inp eqns outp
      Clause-to-FBranch _ = typeErrorS  "Clauses must have exactly one bound pattern."

    Term-to-FTerm : Term -> TC FTerm
    Term-to-FTerm (ok-pat-lam cs) =
      fmap MkRT $ traverse Clause-to-FBranch $ filter not-absurd cs
      where
      not-absurd = \ where
        (absurd-clause _ _) -> false
        _                   -> true
    Term-to-FTerm (meta m args) = blockOnMeta m
    Term-to-FTerm t = typeError (strErr "Only pattern-lambda terms can be reversed." ∷ [])

  open T-to-RT

  module RT-to-T where
    private
      process-tel : Context -> FPat -> Context × List (String × Arg Type)
      process-tel ctx p = helper ctx (p ∷ [])
        where
        helper : Context -> List FPat -> Context × List (String × Arg Type)
        helper ctx [] = ctx , []
        helper ctx (con c ps ∷ ps') =
          let ctx , tel-start = helper ctx ps
              ctx , tel-end   = helper ctx ps' in
              ctx , tel-start ++ tel-end
        helper ctx (var nm ∷ ps) =
          let ctx , tel = helper (ctx -, nm) ps in
          ctx , (nm , varg unknown) ∷ tel

      {-# TERMINATING #-}
      FPat-to-Pattern : Context -> FPat -> TC (Arg Pattern)
      FPat-to-Pattern ctx (con c ps) =
        return ∘ varg ∘ con c =<< traverse (FPat-to-Pattern ctx) ps
      FPat-to-Pattern ctx (var nm) =
        return ∘ varg ∘ var =<< C-lookup ctx nm

      {-# TERMINATING #-}
      FPat-to-Term : Context -> FPat -> TC Term
      FPat-to-Term ctx (con c ps) =
        return ∘ con c ∘ map varg =<< traverse (FPat-to-Term ctx) ps
      FPat-to-Term ctx (var nm) =
        return ∘ (\ x -> var x []) =<< C-lookup ctx nm

    FTerm-to-Term : FTerm -> TC Term
    FTerm-to-Term (MkRT bs) =
      return ∘ ok-pat-lam =<< traverse process-branch bs
      where
      process-term : Context -> List FEqn -> FPat -> TC Term
      process-term ctx [] outp = FPat-to-Term ctx outp
      process-term ctx (MkFEqn argp fn resp ∷ eqns) outp = do
        argp <- FPat-to-Term ctx argp
        fn <- Term'-to-Term ctx fn
        let ctx , res-tel = process-tel ctx resp
        respat <- FPat-to-Pattern ctx resp
        rest-term <- process-term ctx eqns outp
        return (reduced-cons argp fn res-tel respat rest-term)

      process-branch : FBranch -> TC Clause
      process-branch (branch inp eqns outp) = do
        let ctx , tel = process-tel [] inp
        inp <- FPat-to-Pattern ctx inp
        term <- process-term ctx eqns outp
        return (ok-clause tel inp term)

    private
       -- Proof building
      base : (A B : Set) -> (unapply : B -> A) -> (b : B) -> unapply b ≡ unapply b
      base _ _ unapply b = refl

      _P|_|P_ : {A B C : Set} -> {rest : C -> A} {unapply-end : B -> A} -> (b : B)
        -> (f : B <-> C) -> ((c : C) -> rest c ≡ unapply-end (unapply f c))
        -> rest (apply f b) ≡ unapply-end b
      b P| f |P cont with apply f b | unapplyApply f b
      ... | c | refl = cont c

      pattern proof-base `A `B `unapply outp =
        def (quote base) (vArg `A ∷ vArg `B ∷ varg `unapply ∷ varg outp ∷ [])
      pattern proof-cons argpat rev-fn res-tel respat rest-term =
        def (quote _P|_|P_) (
          varg argpat ∷
          varg rev-fn ∷
          varg (ok-pat-lam (ok-clause res-tel respat rest-term ∷ [])) ∷ [])

     -- To construct a proof from a reversible apply function, we
     -- replace _$|_|$_ with _P|_|P_, and the reversible pattern at
     -- the end of apply with base.
    RT-to-proof : (apply : FTerm) (`A `B `unapply : Term) -> TC Term
    RT-to-proof (MkRT bs) `A `B `unapply =
      return ∘ ok-pat-lam =<< traverse process-branch bs
      where
      process-term : Context -> List FEqn -> FPat -> TC Term
      process-term ctx [] outp = do
        outp <- FPat-to-Term ctx outp
        let weaken = weaken (slist-length ctx)
        return (proof-base (weaken `A) (weaken `B) (weaken `unapply) outp)
      process-term ctx (MkFEqn argp fn resp ∷ eqns) outp = do
        argp <- FPat-to-Term ctx argp
        fn <- Term'-to-Term ctx fn
        let ctx , res-tel = process-tel ctx resp
        respat <- FPat-to-Pattern ctx resp
        rest-term <- process-term ctx eqns outp
        return (proof-cons argp fn res-tel respat rest-term)

      process-branch : FBranch -> TC Clause
      process-branch (branch inp eqns outp) = do
        let ctx , tel = process-tel [] inp
        inp <- FPat-to-Pattern ctx inp
        term <- process-term ctx eqns outp
        return (ok-clause tel inp term)
  open RT-to-T

F-tactic : {A B : Set} (apply : A -> B) -> Term -> TC ⊤
F-tactic {A} {B} apply hole = do
  `A <- quoteTC A
  `B <- quoteTC B
  `apply <- quoteTC apply
  apply-rt <- Term-to-FTerm `apply
  let unapply-rt = reverse apply-rt
  `apply   <- FTerm-to-Term apply-rt
  `unapply <- FTerm-to-Term unapply-rt
  `ua <- RT-to-proof apply-rt   `A `B `unapply
  `au <- RT-to-proof unapply-rt `B `A `apply
  unify (con (quote MkF) (map varg (`apply ∷ `unapply ∷ `ua ∷ `au ∷ []))) hole

F : {A B : Set} (apply : A -> B) {@(tactic F-tactic apply) rev : A <-> B} -> A <-> B
F {A} {B} _ {r} = MkF ap unap unapap apunap
  where
  ap : A -> B
  ap = apply r

  unap : B -> A
  unap = unapply r

  unapap : (a : A) -> unap (ap a) ≡ a
  unapap = unapplyApply r

  apunap : (b : B) -> ap (unap b) ≡ b
  apunap = applyUnapply r

----------------------------------------------------------------------
----------------------------- TESTS ----------------------------------
----------------------------------------------------------------------



_>>>R_ : {A B C : Set} -> (A <-> B) -> (B <-> C) -> A <-> C
f >>>R g = F
  \ { a -> a $| f |$ \ { b ->
           b $| g |$ \ { c -> c }}}
infixl 2 _>>>R_

{-
_>>>R_ {A} {B} {C} f g = MkF (
  \ { a -> a $| f |$ \ { b ->
           b $| g |$ \ { c -> c }}}) (
  \ { c -> c $| flip g |$ \ { b ->
           b $| flip f |$ \ { a -> a }}}) (
  \ { a -> _P|_|P_ {unapply-end = \ a -> a} a f \ { b ->
           _P|_|P_ {unapply-end = _} b g \ { c -> base A C (
    \ { c -> c $| flip g |$ \ { b ->
             b $| flip f |$ \ { a -> a }}}) c }}})
  \ { c -> c P| flip g |P \ { b ->
           b P| flip f |P \ { a -> base
    \ { a -> a $| f |$ \ { b ->
             b $| g |$ \ { c -> c }}}) a }}}
infixr 2 _>>>R_
-}

idR : {A : Set} -> A <-> A
idR = F \ { x -> x }

 -- Three different ways to compose two reversibles:
_*R_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> A × B <-> C × D
f *R g = F \ { (a , b) → a $| f |$ \ { c
                       → b $| g |$ \ { d → (c , d) } } }

_+R_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> Either A B <-> Either C D
f +R g = F (\ { (left  a) → a $| f |$ \ { c -> left  c }
              ; (right b) → b $| g |$ \ { d -> right d } })

R≡ : {A B : Set} -> A ≡ B -> A <-> B
R≡ refl = F (\ { x -> x})

private
  pair-swp : {A B : Set} -> A × B <-> B × A
  pair-swp = F \ { (a , b) → (b , a) }

  sum-swp : {A B : Set} -> Either A B <-> Either B A
  sum-swp = F (\ { (left a)  → right a
                 ; (right b) → left b })

  uncurryR : {A B C : Set} -> (A -> B <-> C) -> A × B <-> A × C
  uncurryR f = F (\ {
    (a , b) -> b $| f a |$ \ { c -> (a , c) }})

  uncurryR' : {A : Set} {B C : A -> Set} -> ((a : A) -> B a <-> C a) -> Σ A B <-> Σ A C
  uncurryR' f = F \ { (d , b) → b $| f d |$ \ { c -> (d , c) } }

  data Al : Set where
    `a `b `c `d : Al

  test-nested-sum : Either (Either Nat Nat) (Either Nat Nat) <-> Al × Nat
  test-nested-sum = F (\
    { (left  (left  x)) → x $| flip idR |$ \ { x -> `a , x }
    ; (left  (right x)) → `b , x
    ; (right (left  x)) → `c , x
    ; (right (right x)) → `d , x })

  test-composed : Either (Nat × Nat) Nat <-> Either Nat (Nat × Nat)
  test-composed = F (
    \ { (left (m , n)) -> m $| idR |$ \ { m' ->
                          n $| idR |$ \ { n' -> right (n' , m') }}
      ; (right x)      ->                       left x })
