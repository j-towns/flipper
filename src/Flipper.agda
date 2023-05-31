module Flipper where

open import Prelude hiding (abs; flip)
open import Container.Traversable
open import Tactic.Reflection hiding (VarSet)
open import Tactic.Reflection.DeBruijn

open import Builtin.Reflection

open import Flipper.Parser
open import Flipper.SnocList
open import Flipper.Pack


infix 0 _<->_
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

_⟨_⟩_ : {A B C : Set} -> A -> (A <-> B) -> (B -> C) -> C
a ⟨ f ⟩ g = g (apply f a)

private
   -- Flippable syntax
  data FPat : Set where
    con : (c : Name)(ps : List FPat) -> FPat
    var : (nm : String) -> FPat

  record FOp : Set where
    pattern
    constructor MkFOp
    field
       -- The VarSet stores the names in scope (in particular, it
       -- stores their order). The Term is a pattern lambda
       -- abstraction, the type is a pi-abstraction; both are
       -- abstracted over the VarSet.
      vars : VarSet
      tm : Term
      ty : Type

  record FEqn : Set where
    pattern
    constructor MkFEqn
    field
      argp : FPat
      fn : FOp
      resp : FPat

  record FBranch : Set where
    pattern
    constructor MkFBranch
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
    def (quote _⟨_⟩_) (
      hArg `A ∷
      hArg `B ∷
      hArg _ ∷
      vArg argpat ∷
      vArg rev-fn ∷
      vArg (ok-pat-lam (ok-clause res-tel respat rest-term ∷ [])) ∷ [])

  `<-> : Term -> Term -> Term
  `<-> = def₂ (quote _<->_)

  Parse : Set -> Set -> Set
  Parse A B = A -> QCParser B

  ParseArgs : Set -> Set -> Set
  ParseArgs A B = Parse (List (Arg A)) (List B)

  prsArgs : forall {A B} -> Parse A B -> ParseArgs A B
  prsArgs p []            = pure []
  prsArgs p (vArg x ∷ as) = _∷_ <$> p x <*> prsArgs p as
  prsArgs p (_      ∷ as) = prsArgs p as

  {-# TERMINATING #-}
  prsPat         : Parse     Pattern              FPat
  prsPatVar      : Parse     Nat                  String
  prsArgsPat     : ParseArgs Pattern              FPat
  prsTermPat     : Parse     Term                 FPat
  prsArgsTermPat : ParseArgs Term                 FPat
  prsTermVar     : Parse     Nat                  String
  prsTel         : Parse     Telescope            ⊤
  prsOp          : Parse     (Term × Type × Type) FOp
  prsEqn         : Parse     (Type × Type × Term × Term × Telescope × Pattern) FEqn
  prsBody        : Parse     Term                 (List FEqn × FPat)
  prsClause      : Parse     Clause               FBranch
  prsTerm        : Parse     Term                 FTerm

  prsPat (con c ps) = con c <$> prsArgsPat ps
  prsPat (var x)    = var <$> prsPatVar x
  prsPat p          = qcpError
    (strErr "Patterns must either be variables or constructors, got "
    ∷ pattErr p ∷ [])
  prsPatVar = patVarLookup
  prsArgsPat = prsArgs prsPat

  prsTermPat (var₀ x)     = var <$> prsTermVar x
  prsTermPat (con c args) = con c <$> prsArgsTermPat args
  prsTermPat t            = qcpError
    (strErr "Argument/output must be a variable or constructor, got " ∷
     termErr t ∷ [])
  prsArgsTermPat = prsArgs prsTermPat
  prsTermVar = qcpUse

  prsTel [] = pure unit
  prsTel ((nm , vArg _) ∷ tel) = qcpExtend nm >> prsTel tel
  prsTel (_             ∷ tel) = qcpHExtend   >> prsTel tel

  prsOp (t , `A , `B) =
    MkFOp <$> getVarSet <*> packLamWrap t <*> packPiWrap (`<-> `A `B)

  prsEqn (`A , `B , argp , op , resTel , resp) = do
    argp <- prsTermPat argp
    op <- prsOp (op , `A , `B)
    prsTel resTel
    resp <- prsPat resp
    pure (MkFEqn argp op resp)

  prsBody (ok-body `A `B argp op resTel respat rest-term) = do
    eqn <- prsEqn (`A , `B , argp , op , resTel , respat)
    eqns , outp <- prsBody rest-term
    pure (eqn ∷ eqns , outp)
  prsBody t = [] ,_ <$> prsTermPat t

  prsClause (ok-clause tel inp term) = do
    qcpEmpty
    prsTel tel
    inp <- prsPat inp
    eqns , outp <- prsBody term
    qcpCheckAllUsed
    pure (MkFBranch inp eqns outp)
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

  BaseTemplate : Set
  BaseTemplate = Nat -> Term -> Term

  body : Name -> Term -> Term -> Telescope -> Pattern -> Term -> Term
  body nm argpat rev-fn res-tel respat rest-term =
    def₃ nm argpat rev-fn
      (ok-pat-lam [ ok-clause res-tel respat rest-term ])

  `flip : Term -> Term
  `flip = def₁ (quote flip)

  cmpTel         : Compile FPat Telescope
  cmpPat         : Compile FPat Pattern
  cmpArgPat      : Compile FPat (Arg Pattern)
  cmpPatTerm     : Compile FPat Term
  cmpPatArgTerm  : Compile FPat (Arg Term)
  cmpEqn         : Compile FEqn (Term × Term × Telescope × Pattern)
  cmpEqnF        : Compile FEqn (Term × Term × Telescope × Pattern)
  cmpOp          : Compile FOp  (List Nat)

  {-# TERMINATING #-}
  cmpTel (con c ps) = concat <$> traverse cmpTel ps
  cmpTel (var nm)   = cpExtend nm >> pure [ nm , vArg unknown ]

  cmpPat (con c ps) = con c <$> traverse cmpArgPat ps
  cmpPat (var nm)   = var <$> cpLookup nm
  cmpArgPat p = vArg <$> cmpPat p

  cmpPatTerm (con c ps) = con c <$> traverse cmpPatArgTerm ps
  cmpPatTerm (var nm)   = var₀ <$> cpLookup nm

  cmpPatArgTerm p = vArg <$> cmpPatTerm p

  cmpOp (MkFOp vars _ _) = cpRemap vars

  cmpEqn (MkFEqn argp fn resp) = do
    argp <- cmpPatTerm argp
    vars <- cmpOp fn
    fnLevel <- cpGetIndex
    tel <- cmpTel resp
    resp <- cmpPat resp
    pure (argp , var fnLevel (map (vArg ∘ var₀) vars) , tel , resp)

  cmpEqnF (MkFEqn argp fn resp) = cmpEqn (MkFEqn resp fn argp)

  branchLength : FBranch -> Nat
  branchLength (MkFBranch _ eqns _) = length eqns

  numEqns : FTerm -> Nat
  numEqns (MkFT bs) = sum $ map branchLength bs

  module cmp (bodyName : Name)(baseTemplate : BaseTemplate) where
    cmpBody    : Compile (List FEqn × FPat) Term
    cmpBodyF   : Compile (List FEqn × FPat) Term
    cmpBranch  : Compile FBranch            Clause
    cmpBranchF : Compile FBranch            Clause
    cmp        : Compile FTerm              Term
    cmpF       : Compile FTerm              Term

    {-# TERMINATING #-}
    cmpBody (e ∷ eqns , outp) = do
      cpDown
      (argp , fn , tel , resp) <- cmpEqn e
      rest <- cmpBody (eqns , outp)
      pure (body bodyName argp fn tel resp rest)
    cmpBody ([] , outp) = baseTemplate <$> cpGetDepth <*> cmpPatTerm outp

    cmpBodyF (e ∷ eqns , outp) = do
      (argp , fn , tel , resp) <- cmpEqnF e
      cpUp
      rest <- cmpBodyF (eqns , outp)
      pure (body bodyName argp (`flip fn) tel resp rest)
    cmpBodyF ([] , outp) = baseTemplate <$> cpGetDepth <*> cmpPatTerm outp

    cmpBranch (MkFBranch inp eqns outp) = cpEmpty >>
      ok-clause <$> cmpTel inp <*> cmpPat inp <*> cmpBody (eqns , outp)

    cmpBranchF (MkFBranch inp eqns outp) = cpEmpty >>
      ok-clause <$> cmpTel outp <*> cmpPat outp <*> cmpBodyF (reverse eqns , inp)

    cmp (MkFT bs) = do
      cpSetLevel (sum $ map branchLength bs)
      ok-pat-lam <$> traverse cmpBranch bs

    cmpF (MkFT bs) = do
      cpSetLevel 0
      ok-pat-lam <$> traverse cmpBranchF (reverse bs)
  open cmp

   -- Proof building
  base : (A B : Set) -> (unapply : B -> A) -> (b : B) -> unapply b ≡ unapply b
  base _ _ unapply b = refl

  _P|_|P_ : {A B C : Set} {rest : C -> A} {unapply-end : B -> A} -> (b : B)
    -> (f : B <-> C) -> ((c : C) -> rest c ≡ unapply-end (unapply f c))
    -> rest (apply f b) ≡ unapply-end b
  b P| f |P cont with apply f b | unapplyApply f b
  ... | c | refl = cont c

  `base : Term -> Term -> Term -> BaseTemplate
  `base `A `B `unapply depth outp =
    let weaken = weaken depth in
    def₄ (quote base) (weaken `A) (weaken `B) (weaken `unapply) outp

  getFs : FTerm -> List Term
  getFs (MkFT bs) = FOp.tm ∘ FEqn.fn <$> (FBranch.eqns =<< bs)

  getFTys : FTerm -> List Type
  getFTys (MkFT bs) = FOp.ty ∘ FEqn.fn <$> (FBranch.eqns =<< bs)

  weakenFTys : List Type -> List Type
  weakenFTys tys = map (uncurry weaken) (zip (from 0 for length tys) tys)

  mkTy : Type -> FTerm -> Type
  mkTy hole-ty ft = foldr _`→_ hole-ty $ weakenFTys $ getFTys ft

  mkTel : Nat -> Telescope
  mkTel n = (\ i -> "f" & show i , vArg unknown) <$> from 0 for n

  mkPs : Nat -> List (Arg Pattern)
  mkPs n = map (vArg ∘ var) (reverse (from 0 for n))

  pattern Finner `apply `unapply `ua `au =
    con₄ (quote MkF) `apply `unapply `ua `au
  pattern Fouter ty tel ps inner args =
    def (quote id) (
      hArg unknown ∷ hArg ty ∷
      vArg (pat-lam (clause tel ps inner ∷ []) []) ∷ args)

  ftToFlippable : Type -> Type -> FTerm -> Type -> TC Term
  ftToFlippable `A `B ft hole-ty = do
    `apply   <- cpInTC $ cmp  (quote _⟨_⟩_) (const id) ft
    `unapply <- cpInTC $ cmpF (quote _⟨_⟩_) (const id) ft
    let fs = getFs ft
    let `A = weaken (length fs) `A
    let `B = weaken (length fs) `B
    `ua <- cpInTC $ cmp  (quote _P|_|P_) (`base `A `B `unapply) ft
    `au <- cpInTC $ cmpF (quote _P|_|P_) (`base `B `A `apply)   ft
    let `f = Finner `apply `unapply `ua `au
    let ty = mkTy (weaken (length fs) hole-ty) ft
    return (Fouter ty (mkTel (numEqns ft)) (mkPs (numEqns ft)) `f (map vArg fs))

  FTactic : {A B : Set} (apply : A -> B) -> Tactic
  FTactic {A} {B} apply hole = do
    `A     <- quoteTC A
    `B     <- quoteTC B
    `apply <- quoteTC apply
    ensureNoMetas `A
    ensureNoMetas `B
    ensureNoMetas `apply
    ft <- termToFTerm `apply
    `hole-ty <- inferType hole
    `flippable <- ftToFlippable `A `B ft `hole-ty
    unify `flippable hole

F : {A B : Set} (apply : A -> B) {@(tactic FTactic apply) f : A <-> B} -> A <-> B
F {A} {B} _ {f} = f

----------------------------------------------------------------------
----------------------------- TESTS ----------------------------------
----------------------------------------------------------------------

----------------------------------------------------------------------
private
  idF : {A : Set} -> A <-> A
  idF = F \ { x -> x }

   -- Three different ways to compose two flippables:
  _*F_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> A × B <-> C × D
  f *F g = F \ { (a , b) → a ⟨ f ⟩ \ { c
                         → b ⟨ g ⟩ \ { d → (c , d) } } }

  _+F_ : {A B C D : Set} -> (A <-> C) -> (B <-> D) -> Either A B <-> Either C D
  f +F g = F (\ { (left  a) → a ⟨ f ⟩ \ { c -> left  c }
                ; (right b) → b ⟨ g ⟩ \ { d -> right d } })

  _<>F_ : {A B C : Set} -> (A <-> B) -> (B <-> C) -> A <-> C
  f <>F g = F
    \ { a -> a ⟨ f ⟩ \ { b ->
             b ⟨ g ⟩ \ { c -> c }}}
  infixl 2 _<>F_

  composeF : forall {A C} B -> (A <-> B) -> (B <-> C) -> A <-> C
  composeF _ f g = f <>F g
  syntax composeF B f g = f < B >F g

  F≡ : {A B : Set} -> A ≡ B -> A <-> B
  F≡ refl = F (\ { x -> x})

  pair-swp : {A B : Set} -> A × B <-> B × A
  pair-swp = F \ { (a , b) → (b , a) }

  sum-swp : {A B : Set} -> Either A B <-> Either B A
  sum-swp = F (\ { (left a)  → right a
                 ; (right b) → left b })

  uncurryF : {A B C : Set} -> (A -> B <-> C) -> A × B <-> A × C
  uncurryF f = F (\ {
    (a , b) -> b ⟨ f a ⟩ \ { c -> (a , c) }})

  uncurryF' : {A : Set} {B C : A -> Set} -> ((a : A) -> B a <-> C a) -> Σ A B <-> Σ A C
  uncurryF' f = F \ { (d , b) → b ⟨ f d ⟩ \ { c -> (d , c) } }

  data Al : Set where
    `a `b `c `d : Al

  test-nested-sum : Either (Either Nat Nat) (Either Nat Nat) <-> Al × Nat
  test-nested-sum = F (\
    { (left  (left  x)) → x ⟨ flip idF ⟩ \ { x -> `a , x }
    ; (left  (right x)) → `b , x
    ; (right (left  x)) → `c , x
    ; (right (right x)) → `d , x })

  test-composed : Either (Nat × Nat) Nat <-> Either Nat (Nat × Nat)
  test-composed = F (
    \ { (left (m , n)) -> m ⟨ idF ⟩ \ { m' ->
                          n ⟨ idF ⟩ \ { n' -> right (n' , m') }}
      ; (right x)      ->                       left x })

  test-dependent-types-in-context : {B C : Set} {A : B -> Set} -> (Σ B \ b -> (A b × C)) <-> (Σ B \ b -> (A b × C))
  test-dependent-types-in-context = F \ { (b , a , c) → c ⟨ idF ⟩ \ { c' -> (b , a , c') } }

  test-dependent-pair : forall {A B C} -> ((b : B) -> A <-> C b) ->
    (A × B) <-> Σ B C
  test-dependent-pair f =
    F \ { (a , b) -> a ⟨ f b ⟩ \ { c -> (b , c) }}

  test-empty-branch : ⊤ <-> Either ⊤ ⊥
  test-empty-branch = F \ { x -> left x }

   -- For some reason this has non-visible patterns in it:
  foldrF : forall {n A B} -> (A × B <-> A) -> A × Vec B n <-> A
  foldrF {zero}   f = F \ { (a , [] ) -> a }
  foldrF {suc n}  f = F \ { (a , b ∷ bs) -> (a , bs  ) ⟨ foldrF f  ⟩ \ { a ->
                                            (a , b   ) ⟨ f         ⟩ \ { a -> a } } }

  {-# TERMINATING #-}
  mapF : forall {A B} -> (A <-> B) -> List A <-> List B
  mapF f = F \ { [] -> []
               ; (a ∷ as) -> a  ⟨ f      ⟩ \ { b ->
                             as ⟨ mapF f ⟩ \ { bs -> b ∷ bs } } }
