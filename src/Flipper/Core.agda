module Flipper.Core where

open import Prelude hiding (abs; flip)
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
  flatten (con _ ps) = concatMap flatten ps
  flatten (var nm) = [ nm ]

  record FOp : Set where
    pattern
    constructor MkFOp
    field
      vars : VarSet
      tm : Term
      ty : Type

  record FEqn : Set where
    pattern
    constructor MkFEqn
    field
      argp : FPat
       -- The VarSet stores the names in scope (in particular, it
       -- stores their order). The Term is a pattern lambda
       -- abstraction, the type is a pi-abstraction; both are
       -- abstracted over the VarSet.
      fn : FOp
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
  pattern ok-clause tel inp term = clause tel ((vArg inp) ∷ []) term
  pattern ok-body `A `B argpat rev-fn res-tel respat rest-term =
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

  unArgVisible : forall {A : Set} -> List (Arg A) -> List A
  unArgVisible as = unArg <$> filter isVisible as

  Parse : Set -> Set -> Set
  Parse A B = A -> QCParser B
  
  prsArgPat      : Parse (Arg Pattern)        FPat
  prsPat         : Parse Pattern              FPat
  prsPatVar      : Parse Nat                  String
  prsTermPat     : Parse Term                 FPat
  prsArgsTermPat : Parse (List (Arg Term))    (List FPat)
  prsTermVar     : Parse Nat                  String
  prsTel         : Parse Telescope            ⊤
  prsOp          : Parse (Term × Type × Type) FOp
  prsEqn         : Parse (Type × Type × Term × Term × Telescope × Pattern) FEqn
  prsBody        : Parse Term                 (List FEqn × FPat)
  prsClause      : Parse Clause               FBranch
  prsTerm        : Parse Term                 FTerm

  prsArgPat (vArg p) = prsPat p
  prsArgPat _        = qcpSError "Non-visible pattern."
  
  prsPat (con c ps) = con c <$> traverse prsArgPat ps
  prsPat (var x) = var <$> prsPatVar x
  prsPat p = qcpError
    (strErr "Patterns must either be variables or constructors, got "
    ∷ pattErr p ∷ [])

  prsPatVar = patVarLookup

  {-# TERMINATING #-}
  prsTermPat (var₀ x) = var <$> prsTermVar x
  prsTermPat (con c args) = con c <$> prsArgsTermPat args
  prsTermPat t = qcpError
    (strErr "Argument/output must be a variable or constructor, got " ∷
     termErr t ∷ [])

  prsArgsTermPat args = traverse prsTermPat (unArgVisible args)

  prsTermVar = qcpUse

  prsTel [] = pure unit
  prsTel ((nm , vArg _) ∷ tel) = qcpExtend nm >> prsTel tel
  prsTel ((_ , _) ∷ tel) = qcpHExtend >> prsTel tel

  prsOp (t , `A , `B) =
    MkFOp <$> getVarSet <*> packLamWrap t <*> packPiWrap (def₂ (quote _<->_) `A `B)

  prsEqn (`A , `B , argp , op , resTel , resp) = do
    argp <- prsTermPat argp
    op <- prsOp (op , `A , `B)
    prsTel resTel
    resp <- prsPat resp
    pure (MkFEqn argp op resp)

  prsBody (ok-body `A `B argp op resTel respat rest-term) = do
    eqn <- prsEqn (`A , `B , argp , op , resTel , respat)
    (eqns , outp) <- prsBody rest-term
    pure (eqn ∷ eqns , outp) 
  prsBody t = [] ,_ <$> prsTermPat t

  prsClause (ok-clause tel inp term) = do
    qcpEmpty
    prsTel tel
    inp <- prsPat inp
    (eqns , outp) <- prsBody term
    qcpCheckAllUsed
    pure (branch inp eqns outp)
  prsClause c = qcpSError "Clauses must have exactly one bound pattern."

  prsTerm (ok-pat-lam cs) = do
    cs <- traverse prsClause $ filter not-absurd cs
    pure $ MkFT cs
    where
    not-absurd = \ where
      (absurd-clause _ _) -> false
      _                   -> true
  prsTerm t = qcpSError "Only pattern-lambda terms can be reversed."

  termToFTerm : Term -> TC FTerm
  termToFTerm t with prsTerm t []
  ... | left (_ , ft) = pure ft
  ... | right error = typeError error

  Compile : Set -> Set -> Set
  Compile A B = A -> CParser B

  cmpTel        : Compile FPat Telescope
  cmpPat        : Compile FPat Pattern
  cmpArgPat     : Compile FPat (Arg Pattern)
  cmpPatTerm    : Compile FPat Term
  cmpPatArgTerm : Compile FPat (Arg Term)
  cmpEqn        : Compile FEqn (Term × Term × Telescope × Pattern)
  cmpOp         : Compile FOp  (List Nat)
  cmpBody       : Compile (List FEqn × FPat) Term                 
  cmpBranch     : Compile FBranch            Clause
  cmpTerm       : Compile FTerm              Term

  {-# TERMINATING #-}
  cmpTel (con c ps) = concat <$> traverse cmpTel ps
  cmpTel (var nm) = cpExtend nm >> pure [ nm , vArg unknown ]

  cmpPat (con c ps) = con c <$> traverse cmpArgPat ps
  cmpPat (var nm) = var <$> cpLookup nm
  cmpArgPat p = vArg <$> cmpPat p

  cmpPatTerm (con c ps) = con c <$> traverse cmpPatArgTerm ps
  cmpPatTerm (var nm) = var₀ <$> cpLookup nm

  cmpPatArgTerm p = vArg <$> cmpPatTerm p

  cmpOp (MkFOp vars _ _) = cpRemap vars

  cmpEqn (MkFEqn argp fn resp) = do
    argp <- cmpPatTerm argp
    vars <- cmpOp fn
    fnLevel <- cpGetLevel
    tel <- cmpTel resp
    resp <- cmpPat resp
    pure (argp , var fnLevel (map (vArg ∘ var₀) vars) , tel , resp)

  cmpBody (e ∷ eqns , outp) = do
    cpDown
    (argp , fn , tel , resp) <- cmpEqn e
    rest <- cmpBody (eqns , outp)
    pure (reduced-cons argp fn tel resp rest)
  cmpBody ([] , outp) = cmpPatTerm outp

  cmpBranch (branch inp eqns outp) = cpEmpty >>
    ok-clause <$> cmpTel inp <*> cmpPat inp <*> cmpBody (eqns , outp)

  branch-length : FBranch -> Nat
  branch-length (branch _ eqns _) = length eqns

  num-eqns : FTerm -> Nat
  num-eqns (MkFT bs) = sum $ map branch-length bs

  cmpTerm (MkFT bs) = do
    cpSetLevel (sum $ map branch-length bs)
    cs <- traverse cmpBranch bs
    pure (pat-lam cs [])

  FTerm-to-apply : FTerm -> TC Term
  FTerm-to-apply ft with cmpTerm ft ([] , 0)
  ... | left (_ , t) = pure t
  ... | right error = typeError (strErr error ∷ [])

  module FT-to-T where
    private
      process-tel : QContext -> FPat -> QContext × List (String × Arg Type)
      process-tel ctx p = let flat = flatten p in
        ctx ++S map (vv qone) flat , map (_, varg unknown) flat
        
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

      FTerm-to-unapply : FTerm -> TC Term
      FTerm-to-unapply (MkFT bs) = return ∘ ok-pat-lam =<< traverse process-branch branch-lengths
        where
        branch-lengths = zip (reverse-cumsum (map branch-length bs)) bs
        process-branch : Nat × FBranch -> TC Clause
        process-branch (skip , (branch inp eqns outp)) = do
          let ctx , tel = process-tel [] outp
          outp <- FPat-to-Pattern ctx outp
          term <- process-term 0 ctx (reverse eqns) inp
          return (ok-clause tel outp term)
          where
          process-term : Nat -> QContext -> List FEqn -> FPat -> TC Term
          process-term _ ctx [] outp = snd <$> FPat-to-Term ctx outp
          process-term i ctx (MkFEqn resp (MkFOp vars _ _) argp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- remap-vars ctx vars
            let fn = var (skip + slist-length ctx + i) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- FPat-to-Pattern ctx resp
            rest-term <- process-term (suc i) ctx eqns outp
            return (reduced-cons argp (def (quote flip) (vArg fn ∷ [])) res-tel respat rest-term)

      get-fs : FTerm -> List Term
      get-fs (MkFT bs) = bs >>= \ (branch _ eqns _) -> map (\ (MkFEqn _ (MkFOp _ f _) _) -> f) eqns

      get-f-tys : FTerm -> List Type
      get-f-tys (MkFT bs) = bs >>= \ (branch _ eqns _) -> map (\ (MkFEqn _ (MkFOp _ _ ty) _) -> ty) eqns

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
          return (ok-clause tel inp term)
          where
          process-term : QContext -> List FEqn -> FPat -> TC Term
          process-term ctx [] outp = do
            outp <- snd <$> FPat-to-Term ctx outp
            let weaken = weaken (slist-length ctx)
            return (proof-base (weaken `A) (weaken `B) (weaken `unapply) outp)
          process-term ctx (MkFEqn argp (MkFOp vars _ _) resp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- remap-vars ctx vars
            let fn = var (skip + slist-length ctx + length eqns) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- FPat-to-Pattern ctx resp
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
          return (ok-clause tel outp term)
          where
          process-term : Nat -> QContext -> List FEqn -> FPat -> TC Term
          process-term _ ctx [] outp = do
            outp <- snd <$> FPat-to-Term ctx outp
            let weaken = weaken (slist-length ctx)
            return (proof-base (weaken `B) (weaken `A) (weaken `apply) outp)
          process-term i ctx (MkFEqn resp (MkFOp vars _ _) argp ∷ eqns) outp = do
            ctx , argp <- FPat-to-Term ctx argp
            fn-args <- remap-vars ctx vars
            let fn = var (skip + slist-length ctx + i) (map (varg ∘ var₀) fn-args)
            let ctx , res-tel = process-tel ctx resp
            respat <- FPat-to-Pattern ctx resp
            rest-term <- process-term (suc i) ctx eqns outp
            return (proof-cons argp (def (quote flip) (vArg fn ∷ [])) res-tel respat rest-term)

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
  ensureNoMetas `A
  ensureNoMetas `B
  ensureNoMetas `apply
  ft <- termToFTerm `apply
  `hole-ty <- inferType hole
  `flippable <- FT-to-Flippable `A `B ft `hole-ty

  {-
  ``flippable <- quoteTC `flippable
  ``flippable <- normalise ``flippable
  typeError (termErr `flippable ∷ [])
  -}
  unify `flippable hole

F : {A B : Set} (apply : A -> B) {@(tactic F-tactic apply) f : A <-> B} -> A <-> B
F {A} {B} _ {f} = f

----------------------------------------------------------------------
----------------------------- TESTS ----------------------------------
----------------------------------------------------------------------

----------------------------------------------------------------------
idF : {A : Set} -> A <-> A
idF = F \ { x -> x }

 -- Three different ways to compose two flippables:
_*F_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> A × B <-> C × D
f *F g = F \ { (a , b) → a $| f |$ \ { c
                       → b $| g |$ \ { d → (c , d) } } }

_+F_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> Either A B <-> Either C D
f +F g = F (\ { (left  a) → a $| f |$ \ { c -> left  c }
              ; (right b) → b $| g |$ \ { d -> right d } })

_<>F_ : {A B C : Set} -> (A <-> B) -> (B <-> C) -> A <-> C
f <>F g = F
  \ { a -> a $| f |$ \ { b ->
           b $| g |$ \ { c -> c }}}
infixl 2 _<>F_

composeF : forall {A C} B -> (A <-> B) -> (B <-> C) -> A <-> C
composeF _ f g = f <>F g
syntax composeF B f g = f < B >F g 

F≡ : {A B : Set} -> A ≡ B -> A <-> B
F≡ refl = F (\ { x -> x})

private
  pair-swp : {A B : Set} -> A × B <-> B × A
  pair-swp = F \ { (a , b) → (b , a) }

  sum-swp : {A B : Set} -> Either A B <-> Either B A
  sum-swp = F (\ { (left a)  → right a
                 ; (right b) → left b })

  uncurryF : {A B C : Set} -> (A -> B <-> C) -> A × B <-> A × C
  uncurryF f = F (\ {
    (a , b) -> b $| f a |$ \ { c -> (a , c) }})

  uncurryF' : {A : Set} {B C : A -> Set} -> ((a : A) -> B a <-> C a) -> Σ A B <-> Σ A C
  uncurryF' f = F \ { (d , b) → b $| f d |$ \ { c -> (d , c) } }

  data Al : Set where
    `a `b `c `d : Al

  test-nested-sum : Either (Either Nat Nat) (Either Nat Nat) <-> Al × Nat
  test-nested-sum = F (\
    { (left  (left  x)) → x $| flip idF |$ \ { x -> `a , x }
    ; (left  (right x)) → `b , x
    ; (right (left  x)) → `c , x
    ; (right (right x)) → `d , x })

  test-composed : Either (Nat × Nat) Nat <-> Either Nat (Nat × Nat)
  test-composed = F (
    \ { (left (m , n)) -> m $| idF |$ \ { m' ->
                          n $| idF |$ \ { n' -> right (n' , m') }}
      ; (right x)      ->                       left x })

  test-dependent-types-in-context : {B C : Set} {A : B -> Set} -> (Σ B \ b -> (A b × C)) <-> (Σ B \ b -> (A b × C))
  test-dependent-types-in-context = F \ { (b , a , c) → c $| idF |$ \ { c' -> (b , a , c') } }

  test-dependent-pair : forall {A B C} -> ((b : B) -> A <-> C b) ->
    (A × B) <-> Σ B C
  test-dependent-pair f =
    F \ { (a , b) -> a $| f b |$ \ { c -> (b , c) }}

  test-empty-branch : ⊤ <-> Either ⊤ ⊥
  test-empty-branch = F \ { x -> left x }
