module Flipper.Core where

open import Prelude hiding (abs; flip; Fin; natToFin)
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
  flatten (con c ps) = concatMap flatten ps
  flatten (var nm) = [ nm ]

  record FEqn : Set where
    pattern
    constructor MkFEqn
    field
      argp : FPat
       -- The VarSet stores the names in scope. The Term is a pattern
       -- lambda abstraction, the type is a pi-abstraction; both
       -- are abstracted over the VarSet.
      fn : VarSet × Term × Type
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

   -- We use pattern matching on these 'ok' forms to lossily
   -- transform from Term to FTerm. Any pattern that isn't ok
   -- will throw an error. We use the same ok patterns
   -- to reconstruct a Term from a FTerm...
  pattern ok-pat-lam cs = pat-lam cs []
  pattern ok-clause tel inp term = clause tel (inp ∷ []) term
  pattern ok-cons `A `B argpat rev-fn res-tel respat rest-term =
    def (quote _$|_|$_) (
      harg `A ∷
      harg `B ∷
      harg _ ∷
      varg argpat ∷
      varg rev-fn ∷
      varg (ok-pat-lam (ok-clause res-tel respat rest-term ∷ [])) ∷ [])
  pattern reduced-cons argpat rev-fn res-tel respat rest-term =
    def (quote _$|_|$_) (
      varg argpat ∷
      varg rev-fn ∷
      varg (ok-pat-lam (ok-clause res-tel respat rest-term ∷ [])) ∷ [])

  module T-to-FT where
    private
      pack-vars-pi-wrap : QContext -> Term -> Term -> TC Term
      pack-vars-pi-wrap ctx `A `B = do
        let vars = QC-to-VarSet ctx
        `A <- pack-vars ctx vars `A
        `B <- pack-vars ctx vars `B
        return $ mk-fn-ty (def₂ (quote _<->_) `A `B) vars
        where
        mk-fn-ty : Type -> VarSet -> Type
        mk-fn-ty = slist-foldr
          (\ { nm rest -> pi (vArg unknown) (abs nm rest) })

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
      process-term ctx (ok-cons `A `B argpat rev-fn res-tel respat rest-term) = do
        ctx , argpat <- Term-to-FPat ctx argpat
        `A<->`B <- pack-vars-pi-wrap ctx `A `B
        vars , rev-fn <- pack-vars-lam-wrap ctx rev-fn
        let ctx = qc-extend ctx res-tel
        respat <- Pattern-to-FPat ctx respat
        eqns , outp <- process-term ctx rest-term
        return $ (MkFEqn argpat (vars , rev-fn , `A<->`B) respat ∷ eqns) , outp
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
      FPat-to-Pattern ctx (var nm) = return ∘ var =<< QC-lookup ctx nm

      {-# TERMINATING #-}
      FPat-to-Term : QContext -> FPat -> TC (QContext × Term)
      FPat-to-Term ctx (var nm) = do
        ctx , x <- QC-use' ctx nm
        return (ctx , var₀ x)
      FPat-to-Term ctx (con c ps) = do
        ctx , ts <- helper ctx ps
        return (ctx , (con c (map vArg ts)))
        where
        helper : QContext -> List FPat -> TC (QContext × List Term)
        helper ctx []       = return (ctx , [])
        helper ctx (p ∷ ps) = do
          ctx , t  <- FPat-to-Term ctx p
          ctx , ts <- helper ctx ps
          return (ctx , t ∷ ts)

      remap-vars : QContext -> VarSet -> TC (List Nat)
      remap-vars ctx = helper []
        where
        helper : List Nat -> VarSet -> TC (List Nat)
        helper done [] = return done
        helper done (vars -, nm) = do
          x <- QC-lookup ctx nm
          helper (x ∷ done) vars

      branch-length : FBranch -> Nat
      branch-length (branch _ eqns _) = length eqns

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
          process-term ctx (MkFEqn argp (vars , _) resp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- remap-vars ctx vars
            let fn = var (skip + slist-length ctx + length eqns) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- varg <$> FPat-to-Pattern ctx resp
            rest-term <- process-term ctx eqns outp
            return (reduced-cons argp fn res-tel respat rest-term)

      FTerm-to-unapply : FTerm -> TC Term
      FTerm-to-unapply (MkFT bs) = return ∘ ok-pat-lam =<< traverse process-branch branch-lengths
        where
        branch-lengths = zip (reverse-cumsum (map branch-length bs)) bs
        process-branch : Nat × FBranch -> TC Clause
        process-branch (skip , (branch inp eqns outp)) = do
          let ctx , tel = process-tel [] outp
          outp <- FPat-to-Pattern ctx outp
          term <- process-term 0 ctx (reverse eqns) inp
          return (ok-clause tel (varg outp) term)
          where
          process-term : Nat -> QContext -> List FEqn -> FPat -> TC Term
          process-term _ ctx [] outp = snd <$> FPat-to-Term ctx outp
          process-term i ctx (MkFEqn resp (vars , _) argp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- remap-vars ctx vars
            let fn = var (skip + slist-length ctx + i) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- varg <$> FPat-to-Pattern ctx resp
            rest-term <- process-term (suc i) ctx eqns outp
            return (reduced-cons argp (def (quote flip) (vArg fn ∷ [])) res-tel respat rest-term)

      get-fs : FTerm -> List Term
      get-fs (MkFT bs) = bs >>= \ (branch _ eqns _) -> map (\ (MkFEqn _ (_ , f , _) _) -> f) eqns

      get-f-tys : FTerm -> List Type
      get-f-tys (MkFT bs) = bs >>= \ (branch _ eqns _) -> map (\ (MkFEqn _ (_ , _ , ty) _) -> ty) eqns

      weaken-f-tys : List Type -> List Type
      weaken-f-tys tys = map (uncurry weaken) (zip (from 0 for length tys) tys)

      mk-ty : Type -> FTerm -> Type
      mk-ty hole-ty ft =
        foldr (\ { fn-ty rest -> pi (vArg fn-ty) (abs "_" rest) })
        hole-ty (weaken-f-tys ∘ get-f-tys $ ft)

      mk-tel : Nat -> Telescope
      mk-tel n =
        zip (zipWith _&_ (replicate n "f") (map show (from 0 for n)))
          (replicate n (vArg unknown))

      mk-ps : Nat -> List (Arg Pattern)
      mk-ps n = map (vArg ∘ var) (reverse (from 0 for n))

      num-eqns : FTerm -> Nat
      num-eqns (MkFT bs) = sum $ map branch-length bs

      pattern Finner `apply `unapply `ua `au =
        con₄ (quote MkF) `apply `unapply `ua `au
      pattern Fouter ty tel ps inner args =
        def (quote id) (
          hArg unknown ∷ hArg ty ∷
          vArg (pat-lam (clause tel ps inner ∷ []) []) ∷ args)

       -- Proof building
      base : (A B : Set) -> (unapply : B -> A) -> (b : B) -> unapply b ≡ unapply b
      base _ _ unapply b = refl

      _P|_|P_ : {A B C : Set} {rest : C -> A} {unapply-end : B -> A} -> (b : B)
        -> (f : B <-> C) -> ((c : C) -> rest c ≡ unapply-end (unapply f c))
        -> rest (apply f b) ≡ unapply-end b
      b P| f |P cont with apply f b | unapplyApply f b
      ... | c | refl = cont c

      pattern proof-base `A `B `unapply outp =
        def₄ (quote base) `A `B `unapply outp
      pattern proof-cons argpat rev-fn res-tel respat rest-term =
        def₃ (quote _P|_|P_) 
          argpat
          rev-fn
          (ok-pat-lam (ok-clause res-tel respat rest-term ∷ []))

      FTerm-to-ua : FTerm -> Type -> Type -> Term -> TC Term
      FTerm-to-ua (MkFT bs) `A `B `unapply =
        return ∘ ok-pat-lam =<< traverse process-branch branch-lengths
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
          process-term ctx [] outp = do
            outp <- snd <$> FPat-to-Term ctx outp
            let weaken = weaken (slist-length ctx)
            return (proof-base (weaken `A) (weaken `B) (weaken `unapply) outp)
          process-term ctx (MkFEqn argp (vars , _) resp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- remap-vars ctx vars
            let fn = var (skip + slist-length ctx + length eqns) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- varg <$> FPat-to-Pattern ctx resp
            rest-term <- process-term ctx eqns outp
            return (proof-cons argp fn res-tel respat rest-term)

      FTerm-to-au : FTerm -> Type -> Type -> Term -> TC Term
      FTerm-to-au (MkFT bs) `A `B `apply =
        return ∘ ok-pat-lam =<< traverse process-branch branch-lengths
        where
        branch-lengths = zip (reverse-cumsum (map branch-length bs)) bs
        process-branch : Nat × FBranch -> TC Clause
        process-branch (skip , (branch inp eqns outp)) = do
          let ctx , tel = process-tel [] outp
          outp <- FPat-to-Pattern ctx outp
          term <- process-term 0 ctx (reverse eqns) inp
          return (ok-clause tel (varg outp) term)
          where
          process-term : Nat -> QContext -> List FEqn -> FPat -> TC Term
          process-term _ ctx [] outp = do
            outp <- snd <$> FPat-to-Term ctx outp
            let weaken = weaken (slist-length ctx)
            return (proof-base (weaken `B) (weaken `A) (weaken `apply) outp)
          process-term i ctx (MkFEqn resp (vars , _) argp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- remap-vars ctx vars
            let fn = var (skip + slist-length ctx + i) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- varg <$> FPat-to-Pattern ctx resp
            rest-term <- process-term (suc i) ctx eqns outp
            return (proof-cons argp (def (quote flip) (vArg fn ∷ [])) res-tel respat rest-term)

    {-
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
    FT-to-Flippable : Type -> Type -> FTerm -> Type -> TC Term
    FT-to-Flippable `A `B ft hole-ty = do
      `apply <- FTerm-to-apply ft
      `unapply <- FTerm-to-unapply ft
      let fs = get-fs ft
      let ty = mk-ty (weaken (length fs) hole-ty) ft 
      let `A = weaken (length fs) `A
      let `B = weaken (length fs) `B
      `ua <- FTerm-to-ua ft `A `B `unapply
      `au <- FTerm-to-au ft `A `B `apply
      let `f = Finner `apply `unapply `ua `au
      return (Fouter ty (mk-tel (num-eqns ft)) (mk-ps (num-eqns ft)) `f (map vArg fs))
  open FT-to-T

F-tactic : {A B : Set} (apply : A -> B) -> Term -> TC ⊤
F-tactic {A} {B} apply hole = do
  `A <- quoteTC A
  `B <- quoteTC B
  `apply <- quoteTC apply
  ft <- Term-to-FTerm `apply
  `hole-ty <- inferType hole
  `flippable <- FT-to-Flippable `A `B ft `hole-ty
   -- typeError (termErr {!`flippable!} ∷ [])
  unify `flippable hole

F : {A B : Set} (apply : A -> B) {@(tactic F-tactic apply) f : A <-> B} -> A <-> B
F {A} {B} _ {f} = f

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

{-
encode : forall {A d} mass-fn {{_ : NonZero d}} {{_ : ∀ {a} -> NonZero (mass-fn a)}} -> Dist {A} d mass-fn -> Nat × A <-> Nat
encode {A} {d} mass-fn dist = F \ { (n , a) -> n         $| flip (scale (mass-fn a)) |$ \ { (n , i) -> 
                                               (a , i)   $| dist                     |$ \ { i'      -> 
                                               (n , i')  $| scale d                  |$ \ { n       -> n } } } }
-}
 -- 
 -- encode' : forall {A d} mass-fn {{_ : NonZero d}} {{_ : ∀ {a} -> NonZero (mass-fn a)}} -> Dist {A} d mass-fn -> Nat × A <-> Nat
 -- encode' {A} {d} mass-fn dist =
 --   id {A = (f0 : (a : _) -> Nat <-> Nat × Fin (mass-fn a)) (f1 : (n : _) -> _) (f2 : _) -> Nat × A <-> Nat}
 --   (λ { f0 f1 f2
 --          → MkF
 --            (λ { (n , a)
 --                   → n $| f0 a |$
 --                     (λ { (n , i)
 --                            → (a , i) $| f1 n |$ (λ { i' → (n , i') $| f2 |$ (λ { n → n }) })
 --                        })
 --               })
 --            (λ { n → n $| flip f2 |$
 --                     (λ { (n , i')
 --                            → i' $| flip (f1 n) |$
 --                              (λ { (a , i) → (n , i) $| flip (f0 a) |$ (λ { n → n , a }) })
 --                        })
 --               })
 --      })
 --   (λ { a → flip (scale (mass-fn a)) })
 --   (λ { n → dist })
 --   (λ { → scale d })

{-
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
-}
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
-}

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

_>>>R_ : {A B C : Set} -> (A <-> B) -> (B <-> C) -> A <-> C
f >>>R g = F
  \ { a -> a $| f |$ \ { b ->
           b $| g |$ \ { c -> c }}}
infixl 2 _>>>R_

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

  test-dependent-types-in-context : {B C : Set} {A : B -> Set} -> (Σ B \ b -> (A b × C)) <-> (Σ B \ b -> (A b × C))
  test-dependent-types-in-context = F \ { (b , a , c) → c $| idR |$ \ { c' -> (b , a , c') } }

  test-dependent-pair : forall {A B C} -> ((b : B) -> A <-> C b) ->
    (A × B) <-> Σ B C
  test-dependent-pair f =
    F \ { (a , b) -> a $| f b |$ \ { c -> (b , c) }}
