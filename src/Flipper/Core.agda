module Flipper.Core where

open import Prelude renaming (reverse to list-reverse')
  hiding (abs; flip; Fin; natToFin)
open import Container.Traversable
open import Tactic.Reflection hiding (VarSet)
open import Tactic.Reflection.DeBruijn


open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Bool
 -- open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Nat
  renaming (_+_ to _+N_; _*_ to _*N_; _<_ to _<N_)

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

  {-# TERMINATING #-}
  flatten : FPat -> List String
  flatten (con c ps) = ps >>= flatten
  flatten (var nm) = return nm

  toVarSet : List String -> TC VarSet
  toVarSet = {!!}

  record FEqn : Set where
    pattern
    constructor MkFEqn
    field
      argp : FPat
      fn : Term
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
    constructor MkFT
    field
      branches : List FBranch

   -- Reversal transformation
  reverse-eqn : FEqn -> FEqn
  reverse-eqn (MkFEqn argp fn resp) =
    MkFEqn resp (def (quote flip) (varg fn ∷ [])) argp

  reverse-br : FBranch -> FBranch
  reverse-br (branch inp eqns outp) =
    branch outp (list-reverse' (reverse-eqn <$> eqns)) inp

  reverse : FTerm -> FTerm
  reverse (MkFT branches) = MkFT (reverse-br <$> branches)

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
  pattern flippable `apply = def (quote MkF) (varg `apply ∷ varg unknown ∷ varg unknown ∷ varg unknown ∷ [])

  module T-to-FT where
    private
      qc-extend : QContext -> List (String × Arg Type) -> QContext
      qc-extend = foldl \ ctx -> \ { (nm , varg _) -> ctx -, vv qone nm
                                   ; _             -> ctx -, hv
                                   }

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
          ctx , args <- args-helper ctx args
          return (ctx , (a ∷ args))
      Term-to-FPat ctx (meta m args) = blockOnMeta m
      Term-to-FPat ctx t =
        typeError (strErr "Argument/output must be a variable or constructor" ∷ [])

      process-term : QContext -> Term -> TC (List FEqn × FPat)
      process-term ctx (ok-cons argpat rev-fn res-tel respat rest-term) = do
        ctx , argpat <- Term-to-FPat ctx argpat
        rev-fn <- pack-vars ctx rev-fn
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
      MkFT <$> (traverse Clause-to-FBranch $ filter not-absurd cs)
      where
      not-absurd = \ where
        (absurd-clause _ _) -> false
        _                   -> true
    Term-to-FTerm (meta m args) = blockOnMeta m
    Term-to-FTerm t = typeError (strErr "Only pattern-lambda terms can be reversed." ∷ [])
  open T-to-FT

  module FT-to-T where
    private
      process-tel : QContext -> FPat -> QContext × List (String × Arg Type)
      process-tel ctx p = let flat = flatten p in
        (ctx ++S map (vv qone) flat) , map (_, varg unknown) flat
        
      {-# TERMINATING #-}
      FPat-to-Pattern : QContext -> FPat -> TC Pattern
      FPat-to-Pattern ctx (con c ps) =
        return ∘ con c ∘ map varg =<< traverse (FPat-to-Pattern ctx) ps
      FPat-to-Pattern ctx (var nm) = return ∘ var =<< QC-lookup' ctx nm

      {-# TERMINATING #-}
      FPat-to-Term : QContext -> FPat -> TC (QContext × Term)
      FPat-to-Term ctx (var nm) = do
        ctx , x <- QC-lookup ctx nm
        return (ctx , var₀ x)
      FPat-to-Term ctx (con c ps) = {!!}
         -- return ∘ con c ∘ map varg =<< traverse (FPat-to-Term ctx) ps

      mk-args : QContext -> TC (List Nat)
      mk-args ctx = QC-to-VarSet ctx >>= remap-vars ctx
        where
        remap-vars : QContext -> VarSet -> TC (List Nat)
        remap-vars ctx = helper []
          where
          helper : List Nat -> VarSet -> TC (List Nat)
          helper done [] = return done
          helper done (vars -, nm) = do
            x <- QC-lookup' ctx nm
            helper (x ∷ done) vars

      branch-length : FBranch -> Nat
      branch-length (branch _ eqns _) = length eqns

      reverse-cumsum : List Nat -> List Nat
      reverse-cumsum []       = []
      reverse-cumsum (x ∷ xs) = case reverse-cumsum xs of \ where
        []           -> [ 0 ]
        (sum ∷ rest) -> x + sum ∷ sum ∷ rest

      FTerm-to-apply : FTerm -> TC Term
      FTerm-to-apply (MkFT bs) = return ∘ ok-pat-lam =<< traverse process-branch branch-lengths
        where
        branch-lengths = zip (reverse-cumsum (map branch-length bs)) bs
        process-branch : Nat × FBranch -> TC Clause
        process-branch (skip , (branch inp eqns outp)) = do
          let ctx , tel = process-tel [] inp
          inp <- FPat-to-Pattern ctx inp
          term <- process-term ctx eqns outp
          return (ok-clause tel (varg inp) term)
          where
          process-term : QContext -> List FEqn -> FPat -> TC Term
          process-term ctx [] outp = snd <$> FPat-to-Term ctx outp
          process-term ctx (MkFEqn argp fn resp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- mk-args ctx
            let fn = var (skip + slist-length ctx + length eqns) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- varg <$> FPat-to-Pattern ctx resp
            rest-term <- process-term ctx eqns outp
            return (reduced-cons argp fn res-tel respat rest-term)

      get-fs : FTerm -> List Term
      get-fs (MkFT bs) = bs >>= (\ (branch _ eqns _) -> map (\ (MkFEqn _ f _) -> f) eqns )

    FT-to-Flippable : FTerm -> TC Term
    FT-to-Flippable ft = do
      `apply <- FTerm-to-apply ft
      let fs = get-fs ft
      let `term = def (quote id) (hArg unknown ∷ hArg {!!} ∷ vArg (pat-lam (clause {!!} {!!} {!!} ∷ []) []) ∷ [])
      let `f = flippable `apply
      {!!}
     

     -- Proof building
    base : (A B : Set) -> (unapply : B -> A) -> (b : B) -> unapply b ≡ unapply b
    base _ _ unapply b = refl

    _P|_|P_ : {A B C : Set} {rest : C -> A} {unapply-end : B -> A} -> (b : B)
      -> (f : B <-> C) -> ((c : C) -> rest c ≡ unapply-end (unapply f c))
      -> rest (apply f b) ≡ unapply-end b
    b P| f |P cont with apply f b | unapplyApply f b
    ... | c | refl = cont c

    {-
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
    FT-to-proof : (apply : FTerm) (`A `B `unapply : Term) -> TC Term
    FT-to-proof (MkFT bs) `A `B `unapply =
      return ∘ ok-pat-lam =<< traverse process-branch bs
      where
      process-term : Context -> List FEqn -> FPat -> TC Term
      process-term ctx [] outp = do
        outp <- FPat-to-Term ctx outp
        let weaken = weaken (slist-length ctx)
        return (proof-base (weaken `A) (weaken `B) (weaken `unapply) outp)
      process-term ctx (MkFEqn argp fn resp ∷ eqns) outp = do
        argp <- FPat-to-Term ctx argp
        fn <- {!!} ctx fn
        let ctx , res-tel = process-tel ctx resp
        respat <- fmap varg $ FPat-to-Pattern ctx resp
        rest-term <- process-term ctx eqns outp
        return (proof-cons argp fn res-tel respat rest-term)

      process-branch : FBranch -> TC Clause
      process-branch (branch inp eqns outp) = do
        let ctx , tel = process-tel [] inp
        inp <- fmap varg $ FPat-to-Pattern ctx inp
        term <- process-term ctx eqns outp
        return (ok-clause tel inp term)
    -}
  open FT-to-T

F-tactic : {A B : Set} (apply : A -> B) -> Term -> TC ⊤
F-tactic {A} {B} apply hole = do
  `A <- quoteTC A
  `B <- quoteTC B
  `apply <- quoteTC apply
  ft <- Term-to-FTerm `apply
  `flippable <- FT-to-Flippable ft
  unify `flippable hole

F : {A B : Set} (apply : A -> B) {@(tactic F-tactic apply) rev : A <-> B} -> A <-> B
F {A} {B} _ {r} = r

----------------------------------------------------------------------
----------------------------- TESTS ----------------------------------
----------------------------------------------------------------------

----------------------------------------------------------------------
private
  open import Numeric.Nat.DivMod
  open import Tactic.Nat
  
  
  record Range (a b : Nat) : Set where
    constructor _[[_,_]]
    field
      n   : Nat
      a≤n : a ≤ n
      n<b : n < b
  
  natToRange : forall {a b} n {{_ : IsTrue (a <? suc n && n <? b)}}
    -> Range a b
  natToRange {a} {b} n with compare a (suc n) | compare n b
  ... | less a≤n | less n<b = n [[ a≤n , n<b ]]
  
  instance
    NumberRange : forall {a b} -> Number (Range a b)
    Number.Constraint (NumberRange {a} {b}) n = IsTrue (a <? suc n && n <? b)
    fromNat {{NumberRange}} = natToRange
  
    ShowRange : forall {a b} -> Show (Range a b)
    ShowRange = simpleShowInstance \ (n [[ _ , _ ]]) -> show n 
  
  cong-Range : forall {a b} {m n : Range a b}
    -> Range.n m ≡ Range.n n -> m ≡ n
  cong-Range {m = m [[ a≤m , m<b ]]} {n = n [[ a≤n , n<b ]]} m≡n
    rewrite m≡n | smashed {x = a≤m} {y = a≤n}
      | smashed {x = m<b} {y = n<b} = refl
  
  Fin : Nat -> Set
  Fin d = Range 0 d
  
  natToFin : forall {d} n {{_ : IsTrue (n <? d)}} -> Fin d
  natToFin = natToRange
  
  scale : forall d {{_ : NonZero d}} -> Nat × Fin d <-> Nat
  scale d = MkF ap unap unap-ap ap-unap
    where
    ap : Nat × Fin d -> Nat
    ap (q , r [[ _ , _ ]]) = q * d + r
  
    unap : Nat -> Nat × Fin d
    unap n with n divmod d
    unap n | dm = quot dm , (rem dm [[ auto , rem-less dm ]])
  
    unap-ap : (qr : Nat × Fin d) -> unap (ap qr) ≡ qr
    unap-ap (q , (r [[ _ , r<d ]])) with ((q * d + r) divmod d)
    ... | dm with divmod-unique dm (qr q r r<d refl)
    ...   | q'=q , r'=r = cong₂ _,_ q'=q (cong-Range r'=r)
  
    ap-unap : (n : Nat) -> ap (unap n) ≡ n
    ap-unap n = quot-rem-sound (n divmod d)
  
  Dist : forall {A : Set} -> Nat -> (A -> Nat) -> Set
  Dist d mass-fn = (∃ a , Fin (mass-fn a)) <-> Fin d

 -- encode : forall {A d} mass-fn {{_ : NonZero d}} {{_ : ∀ {a} -> NonZero (mass-fn a)}} -> Dist {A} d mass-fn -> Nat × A <-> Nat
 -- encode mass-fn dist = F \ { (n , a) -> n         $| flip (scale (mass-fn a)) |$ \ { (n , i) -> 
 --                                        (a , i)   $| dist                     |$ \ { i'      -> 
 --                                        (n , i')  $| scale _                  |$ \ { n       -> n } } } }

encode' : forall {A d} mass-fn {{_ : NonZero d}} {{_ : ∀ {a} -> NonZero (mass-fn a)}} -> Dist {A} d mass-fn -> Nat × A <-> Nat
encode' {A} {d} mass-fn dist =
  id {A = ((a : _) -> _) -> ((n : _) -> _) -> _ -> _}
      (\ { f1 f2 f3 -> MkF (\ { (n , a) -> n        $| f1 a |$ \ { (n , i) -> 
                                           (a , i)  $| f2 n |$ \ { i'      -> 
                                           (n , i') $| f3   |$ \ { n       -> n } } } })

                     (\ { n -> n       $| flip f3     |$ \ { (n , i') -> 
                               i'      $| flip (f2 n) |$ \ { (a , i)  -> 
                               (n , i) $| flip (f1 a) |$ \ { n        -> (n , a) } } } })

                     (\ { (n , a)  -> n        P| f1 a |P \ { (n , i) -> 
                                      (a , i)  P| f2 n |P \ { i'      -> 
                                      (n , i') P| f3   |P \ { n -> base _ _ ( \ { n -> n       $| flip f3     |$ \ { (n , i') -> 
                                                                                       i'      $| flip (f2 n) |$ \ { (a , i)  -> 
                                                                                       (n , i) $| flip (f1 a) |$ \ { n        -> (n , a) } } } }) n } } } })
                     {!!}}) (\ { a -> flip (scale (mass-fn a))})
                            (\ { n -> dist })
                            (scale _)
{-
  apply
  (flip
   (flip
    (scale
     (mass-fn
      (fst (apply (flip dist) (snd (apply (flip (scale d)) n))))))))
  (fst (apply (flip (scale d)) n) ,
   snd (apply (flip dist) (snd (apply (flip (scale d)) n))))
  , fst (apply (flip dist) (snd (apply (flip (scale d)) n)))
    = _unapply-end_1694 (unapply (scale d) n)
    : Σ Nat (λ _ → A)

    (blocked on _unapply-end_1694)


  _unapply-end_1694 (n₁ , i') = _unapply-end_1679 (unapply dist i')
    : Σ Nat (λ _ → A)

    (blocked on any(_unapply-end_1679, _unapply-end_1694))


  _unapply-end_1679 (a , i)
    = _unapply-end_1664 (unapply (flip (scale (mass-fn a))) (n₁ , i))
    : Σ Nat (λ _ → A)

    (blocked on any(_unapply-end_1664, _unapply-end_1679))


  _unapply-end_1664 n = n , a : Σ Nat (λ _ → A)

    (blocked on _unapply-end_1664)
-}

{-
interweave : forall {A B C} -> (f : C -> A <-> A × B) -> (g : C × B <-> B) -> (h : A × B <-> A) -> A × C <-> A
interweave f g h = MkF
  (\ { (n , a) -> n        $| f a |$ \ { (n , i) -> 
                  (a , i)  $| g   |$ \ { i'      -> 
                  (n , i') $| h   |$ \ { n       -> n } } } })
  ( \ { n -> n       $| flip h     |$ \ { (n , i') -> 
             i'      $| flip g     |$ \ { (a , i)  -> 
             (n , i) $| flip (f a) |$ \ { n        -> (n , a) } } } })
  (\ { (n , a)  -> _P|_|P_ n        (f a) \ { (n , i) -> 
                   _P|_|P_ (a , i)  g     \ { i' -> 
                   _P|_|P_ (n , i') h     \ { n -> base (Nat × A) Nat {!!} n } } } })
  {!!}
----------------------------------------------------------------------

_>>>R_ : {A B C : Set} -> (B <-> A) -> (B <-> C) -> A <-> C
f >>>R g = F
  \ { a -> a $| flip f |$ \ { b ->
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
-}
