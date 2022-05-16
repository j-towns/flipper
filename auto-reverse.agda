open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)

open import Term using (Term'; Type'; Term-to-Term'; Term'-to-Term)


pattern default-modality = modality relevant quantity-ω

 -- In various places varg is the only type of arg we support
pattern varg x = arg (arg-info visible   default-modality) x
pattern harg x = arg (arg-info hidden    default-modality) x
pattern iarg x = arg (arg-info instance′ default-modality) x

str-eq : String -> String -> Bool
str-eq = primStringEquality

record One : Set where
  constructor <>

data _+_ (A B : Set) : Set where
 inl : A -> (A + B)
 inr : B -> (A + B)

_*_ : Set -> Set -> Set
A * B = Σ A \ _ -> B

infixr 4 _+_
infixr 5 _*_

data SnocList (A : Set) : Set where
  [] : SnocList A
  _-,_ : SnocList A -> A -> SnocList A

infixl 1 _-,_

Telescope : Set
Telescope = List (String * Type)

Context : Set
Context = SnocList (String * Type)

 -- TODO: Import these list functions from somewhere else...
list-map : {A B : Set} -> (A -> B) -> List A -> List B
list-map f [] = []
list-map f (a ∷ as) = f a ∷ (list-map f as)

list-reverse : {A : Set} -> List A -> SnocList A
list-reverse = go []
  where go : {A : Set} -> SnocList A -> List A -> SnocList A
        go acc [] = acc
        go acc (a ∷ as) = go (acc -, a) as

slist-index : {A : Set} -> Nat -> SnocList A -> TC A
slist-index _       []       = typeError (strErr "List index error" ∷ [])
slist-index zero    (_ -, a)  = returnTC a
slist-index (suc n) (as -, _) = slist-index n as

list-concat : {A : Set} -> List (List A) -> List A
list-concat [] = []
list-concat ([] ∷ ass) = list-concat ass
list-concat ((a ∷ as) ∷ ass) = a ∷ list-concat (as ∷ ass)

 -- Reversible syntax
data RevPat : Set where
  con : (c : Name) (ps : List RevPat) -> RevPat
  var : (x : Nat)                     -> RevPat
   -- TODO: Add absurd

RevFn : Set
RevFn = Term * Type * Type

data RevBranch : Set where
  bottom : (tel : List (String * Type)) (inp : RevPat)
    -> (outp : RevPat) -> RevBranch
  cons : (tel : List (String * Type)) (inp argp : RevPat)
    -> (rev-fn : RevFn) (rest : RevBranch) -> RevBranch

{-
eg-rev = (\ x ->
    x $| rev-fn2 |$ (\ (y , z) ->
    y $| rev-fn1 |$ (\ w
  -> w , z)))
-}

 -- Only allow branching at the top level of a reversible term.
 -- I think this will simplify the reversal transformation and
 -- make definitions more readable, but maybe we can relax this later.
record RevTerm : Set where
  constructor top
  field
    branches : List RevBranch
    inty outty : Type

reverse-tactic : {A B : Set} (apply : A -> B) -> Term -> TC ⊤

record _<->_ (A B : Set) : Set where
  constructor MkRev
  field
    apply   : A -> B
    @(tactic (reverse-tactic apply)) {unapply} : B -> A
    {-
    TODO: require the proofs
    unapplyApply : (a : A) -> unapply (apply a) == a
    applyUnapply : (b : B) -> apply (unapply b) == b
    -}

open _<->_
infix 1 _<->_

un : {A B : Set} -> (A <-> B) -> B <-> A
un f = MkRev (unapply f) {apply f}

_$|_|$_ : {A B C : Set} -> A -> (A <-> B) -> (B -> C) -> C
a $| f |$ g = g (apply f a)

 -- We use pattern matching on these 'ok' forms to lossily
 -- transform from Term to RevTerm. Any pattern that isn't ok
 -- will throw an error. We use the same ok patterns
 -- to reconstruct a Term from a RevTerm...
pattern ok-pat-lam cs = pat-lam cs []
pattern ok-clause tel inp term = clause tel ((varg inp) ∷ []) term
pattern ok-cons argty outty-local outty argp rev-fn rest-clause =
  def (quote _$|_|$_) (
          harg argty ∷
          harg outty-local ∷
          harg outty ∷
          varg argp ∷
          varg rev-fn ∷
          varg (pat-lam (rest-clause ∷ []) []) ∷ [])


non-lam-err : ∀ {a} {A : Set a} -> Term -> TC A
non-lam-err t = typeError
  (strErr "Auto-reverse only supports (unapplied) pattern matching lambda term inputs,
  but received " ∷ termErr t ∷ [])

too-many-params-err : ∀ {a} {A : Set a} -> TC A
too-many-params-err = typeError (strErr "Lambda term has more than one param." ∷ [])

too-few-params-err : ∀ {a} {A : Set a} -> TC A
too-few-params-err = typeError (strErr "Lambda term has zero params." ∷ [])

param-err : ∀ {a} {A : Set a} -> TC A
param-err = typeError (strErr "Parameter has incorrect form." ∷ [])

lam-term-err : ∀ {a} {A : Set a} (String) -> TC A
lam-term-err s = typeError (strErr "Lambda term has incorrect form." ∷
  strErr s ∷ [])

explicit-pattern-error :  ∀ {a} {A : Set a} -> TC A
explicit-pattern-error = typeError (strErr "For now only explicit arguments are allowed in patterns" ∷ [])

tel-explicit-error : ∀ {a} {A : Set a} -> TC A
tel-explicit-error = typeError (strErr "Implicit/instance arg found in telescope." ∷ [])

mapTC : {A B : Set} -> (A -> TC B) -> List A -> TC (List B)
mapTC f [] = returnTC []
mapTC f (a ∷ as) = bindTC (f a) \ b ->
                   bindTC (mapTC f as) \ bs ->
                   returnTC (b ∷ bs)

mapRP : (Nat -> TC Nat) -> RevPat -> TC RevPat
mapRP f (con c ps) = 
  bindTC (helper ps) \ fps ->
  returnTC (con c fps)
  where
  helper : List RevPat -> TC (List RevPat)
  helper [] = returnTC []
  helper (p ∷ ps) = 
    bindTC (mapRP f p) \ fp ->
    bindTC (helper ps) \ fps ->
    returnTC (fp ∷ fps)
mapRP f (var x) = 
  bindTC (f x) \ fx ->
  returnTC (var fx)

strip-info : {A : Set} -> Arg A -> A
strip-info (arg _ x) = x

Term-to-RevTerm : Term -> (inty outty : Type) -> TC RevTerm
Term-to-RevTerm (ok-pat-lam cs) inty outty =
    bindTC (mapTC to-RevBranch cs) \ bs ->
    returnTC (top bs inty outty)
  where
  Pattern-to-RevPat : Pattern -> TC RevPat
  Pattern-to-RevPat (con c ps) = 
    bindTC (helper ps) \ ps ->
    returnTC (con c ps)
    where
    helper : List (Arg Pattern) -> TC (List RevPat)
    helper [] = returnTC []
    helper ((varg p) ∷ ps) =
      bindTC (Pattern-to-RevPat p) \ p -> 
      bindTC (helper ps) \ ps -> returnTC (p ∷ ps)
    helper _ = explicit-pattern-error
  Pattern-to-RevPat (var x) = returnTC (var x)
  Pattern-to-RevPat (absurd x) = {!!}
  Pattern-to-RevPat _ = param-err

  Term-to-RevPat : Term -> TC RevPat
  Term-to-RevPat (var x [])   = returnTC (var x)
  Term-to-RevPat (con c args) = 
    bindTC (process-subterms args) \ args -> returnTC (con c args)
    where
    process-subterms : List (Arg Term) -> TC (List RevPat)
    process-subterms [] = returnTC []
    process-subterms (harg unknown ∷ args) = process-subterms args
    process-subterms (harg _       ∷ args) =
      typeError (strErr "Explicitly providing implicit arguments to constructors is not supported." ∷ [])
    process-subterms (iarg unknown ∷ args) = process-subterms args
    process-subterms (iarg _       ∷ args) =
      typeError (strErr "Explicitly providing instance arguments to constructors is not supported." ∷ [])
    process-subterms (varg a ∷ args) =
      bindTC   (Term-to-RevPat  a)    \ a    ->
      bindTC   (process-subterms args) \ args ->
      returnTC (a ∷ args)
    process-subterms _ = typeError (strErr "Unsupported arg info in subterm." ∷ [])
  Term-to-RevPat t = lam-term-err "Converting term to pattern."

  to-RevBranch : Clause -> TC RevBranch
  process-term : Term -> TC (RevPat + (RevPat * RevFn * RevBranch))
  process-term (ok-cons argty outty _ argp rev-fn rest-clause) =
    bindTC (Term-to-RevPat argp) \ argp ->
    bindTC (to-RevBranch rest-clause) \ rest ->
    returnTC (inr (argp , (rev-fn , argty , outty) , rest))
  process-term t =
    bindTC (Term-to-RevPat t) \ p ->
    returnTC (inl p)

  to-RevBranch (ok-clause tel inp t) =
    bindTC (mapTC (\ { (n , varg a) -> returnTC (n , a)
                     ; _            -> tel-explicit-error }) tel) \ tel ->
    bindTC (Pattern-to-RevPat inp) \ inp ->
    bindTC (process-term t) \ 
      { (inl outp)                   -> returnTC (bottom tel inp outp)
      ; (inr (argp , rev-fn , rest)) -> returnTC (cons tel inp argp rev-fn rest)
      }
  to-RevBranch (absurd-clause tel ps) = {!!}
  to-RevBranch (clause tel (p ∷ []) t) = explicit-pattern-error
  to-RevBranch (clause tel [] t) = too-few-params-err -- Can this happen?
  to-RevBranch (clause tel (_ ∷ _ ∷ _) _) = too-many-params-err
Term-to-RevTerm t _ _ = non-lam-err t

RevTerm-to-Term : RevTerm -> TC Term
RevTerm-to-Term (top branches _ outty) =
  bindTC (mapTC (process-branch outty) branches) \ cs ->
  returnTC (ok-pat-lam cs)
  where
  RevPat-to-Term : RevPat -> TC Term
  RevPat-to-Term (con c ps) = 
    bindTC (getType c) \ ty ->
    bindTC (fill-unknowns ty ps) \ args ->
    returnTC (con c args)
    where
    fill-unknowns : Type -> List RevPat -> TC (List (Arg Term))
    fill-unknowns (pi (varg _) (abs _ ty)) (p ∷ ps) =
      bindTC (RevPat-to-Term p) \ t ->
      bindTC (fill-unknowns ty ps) \ args ->
      returnTC (varg t ∷ args)
    fill-unknowns (pi (harg _) (abs _ ty)) ps =
      bindTC (fill-unknowns ty ps) \ args ->
      returnTC (harg unknown ∷ args)
    fill-unknowns (pi (iarg _) (abs _ ty)) ps = 
      bindTC (fill-unknowns ty ps) \ args ->
      returnTC (iarg unknown ∷ args)
    fill-unknowns _ [] = returnTC []
    fill-unknowns _ _  = typeError (strErr "Error filling constructor unknown args." ∷ [])
  RevPat-to-Term (var x) = returnTC (var x [])

  RevPat-to-Pattern : RevPat -> Pattern
  RevPat-to-Pattern (con c ps) = con c (helper ps)
    where
    helper : List RevPat -> List (Arg Pattern)
    helper [] = []
    helper (p ∷ ps) = (varg (RevPat-to-Pattern p)) ∷ helper ps
  RevPat-to-Pattern (var x) = var x

  mk-clause : Telescope -> RevPat -> Term -> Clause
  mk-clause tel inp t =
    ok-clause (list-map (\ (n , ty) -> n , varg ty) tel) (RevPat-to-Pattern inp) t

  process-branch : (outty : Type) -> RevBranch -> TC Clause
  process-branch _ (bottom tel inp outp) =
    bindTC (RevPat-to-Term outp) \ outp ->
    returnTC (mk-clause tel inp outp)
  process-branch outty (cons tel inp argp (rev-fn , argty , outty-local) rest) = 
    bindTC (RevPat-to-Term argp) \ argp ->
    bindTC (process-branch outty rest) \ rest-clause ->
    returnTC (mk-clause tel inp (ok-cons argty outty-local outty argp rev-fn rest-clause))

fn-to-RevTerm : {A B : Set} -> (apply : A -> B) -> TC RevTerm
fn-to-RevTerm {A} {B} apply = 
  bindTC (quoteTC apply) \ apply-term ->
  bindTC (quoteTC A) \ A-term ->
  bindTC (quoteTC B) \ B-term ->
  (Term-to-RevTerm apply-term A-term B-term)

 -- Map name to De Bruijn index.
lookup : String -> Context -> TC Nat
lookup = go 0
  where go : Nat -> String -> Context -> TC Nat
        go n s [] = typeError (strErr "Telescope lookup error" ∷ [])
        go n s (tel -, (r , _)) with str-eq s r
        ... | false = go (suc n) s tel
        ... | true  = returnTC n

update-debruijn : Context -> Context -> RevPat -> TC RevPat
update-debruijn oldctx newctx = mapRP \ x ->
  bindTC (slist-index x oldctx) \ (nm , _) -> 
  lookup nm newctx

Level : Set
Level = Nat + Nat -- Left branch represents negative levels,
                  -- right branch non-negative.

idx-to-lvl : (depth : Nat) -> Nat -> Level
idx-to-lvl depth       zero      = inr depth 
idx-to-lvl zero        (suc idx) = inl idx
idx-to-lvl (suc depth) (suc idx) = idx-to-lvl depth idx

idx-to-lvl' : (depth : Nat) -> Nat -> TC Nat
idx-to-lvl' depth       zero      = returnTC depth
idx-to-lvl' zero        (suc idx) = typeError {!!}
idx-to-lvl' (suc depth) (suc idx) = idx-to-lvl' depth idx

lvl-to-idx : (depth : Nat) -> Level -> Nat
lvl-to-idx depth (inl level) = {!!}
lvl-to-idx depth (inr level) = {!!}

 -- Turn a branch 'inside-out'
reverse-branch : RevBranch -> TC RevBranch
reverse-branch (bottom tel inp outp) =
  let ctx = list-reverse tel in
  bindTC (make-newtel ctx outp) \ (newtel , perm) ->
  let newctx = list-reverse newtel in
  bindTC (update-debruijn ctx newctx inp) \ newoutp -> 
  bindTC (update-debruijn ctx newctx outp) \ newinp -> 
  returnTC (bottom newtel newinp newoutp)
  where
  make-newtel : Context -> RevPat -> TC (Telescope * List Nat)
  make-newtel ctx (con _ ps) = 
    bindTC (helper ps) returnTC 
    where
    helper : List RevPat -> TC (Telescope * List Nat)
    helper [] = returnTC ([] , [])
    helper (p ∷ ps) =
      bindTC (make-newtel ctx p) \ (newtel , newperm) ->
      bindTC (helper ps) \ (newtels , newperms) ->
      returnTC ((list-concat (newtel  ∷ newtels  ∷ [])) , 
                 list-concat (newperm ∷ newperms ∷ []))
  make-newtel ctx (var x) =
    bindTC (slist-index x ctx) \ nmty ->
    returnTC (nmty ∷ [] , x ∷ [])
 
 -- Strategy here:
 --   First compute the full context for the reversed
 --   branch. We need to do this so that we can replace
 --   binders with correct de Bruijn indices. Hopefully
 --   during this pass we can also check for non-linearity.
 --   need to particularly watch out for multiple usage
 --   (as opposed to zero usage), because I multi-use
 --   could cause silent failure (it would basically result
 --   in shadowing). The variables at the beginning of
 --   the old branch need to be at the outermost layer of
 --   the new context list as they will be processed first.
 --
 --   Simultaneously work forwards through the old branch
 --   and the new full context to generate the new branch.
 --   It will be necessary to build up a full copy of the old
 --   context as we work down, so that variables can be looked
 --   up using their old de Bruijn indices.
reverse-branch (cons tel inp argp rev-fn rest) =
  let telr = list-reverse tel in
  rec {!!} rest
  where
  mktel : Telescope -> RevPat -> Telescope
  mktel p = {!!}

  rec : (reversed rest : RevBranch) -> TC RevBranch
  rec reversed rest = {!!}

reverse : RevTerm -> TC RevTerm
reverse (top branches inty outty) = 
  bindTC (mapTC reverse-branch branches) \ branches ->
  returnTC (top branches outty inty)

reverse-tactic apply hole =
  bindTC (fn-to-RevTerm apply) \ t ->
  bindTC (reverse t) \ rt ->
  bindTC (RevTerm-to-Term rt)
  {-
  bindTC (quoteTC t) \ t' ->
  bindTC (normalise t') \ t' ->
  bindTC getContext \ ctx ->
  bindTC (quoteTC ctx) \ ctx' ->
  typeError ({!termErr ctx'!} ∷ [])
  -}
   --
  (unify hole)
  


 -- TESTS

 -- Test the round-trip Agda code -> Term -> RevTerm -> Agda code
dont-reverse : {A B : Set} (apply : A -> B) -> Term -> TC ⊤
dont-reverse {A} {B} apply hole =
  bindTC (quoteTC apply) \ apply-term ->
  bindTC (quoteTC A) \ A-term ->
  bindTC (quoteTC B) \ B-term ->
  bindTC (Term-to-RevTerm apply-term A-term B-term) \ rt ->
  bindTC (RevTerm-to-Term rt) \ t ->
  unify hole t

record _->'_ (A B : Set) : Set where
  field
    apply   : A -> B
    @(tactic (dont-reverse apply)) {apply'} : A -> B
open _->'_

dont-reverse-id : Nat ->' Nat
dont-reverse-id = record { apply = \ { x -> x } }

test-dont-reverse-id-1 : (x : Nat) -> apply dont-reverse-id x ≡ x
test-dont-reverse-id-1 x = refl

test-dont-reverse-id-2 : (x : Nat) -> apply' dont-reverse-id x ≡ x
test-dont-reverse-id-2 x = refl

dont-reverse-swap : (Nat * Nat) ->' (Nat * Nat)
dont-reverse-swap = record { apply = \ { (x , y) -> y , x } }

test-dont-reverse-swap-1 : (x y : Nat) -> apply dont-reverse-swap (x , y) ≡ (y , x)
test-dont-reverse-swap-1 x y = refl

test-dont-reverse-swap-2 : (x y : Nat) -> apply' dont-reverse-swap (x , y) ≡ (y , x)
test-dont-reverse-swap-2 x y = refl

rev-fn1 : Nat <-> Nat
rev-fn1 = {!!} {-record { apply   = \ x -> x
                 ; unapply = \ x -> x}-}

dont-reverse-nested : Nat ->' Nat
dont-reverse-nested = record { apply = \ { x -> x $| rev-fn1 |$ \ { y -> y }}}

 -- test-dont-reverse-nested

rev-fn2 : Nat <-> (Nat * (Nat * Nat))
rev-fn2 = {!!}

rev-fn3 : (Nat * Nat) <-> Nat
rev-fn3 = {!!}

{-

eg-rev = (\ x ->
    x $| rev-fn2 |$ (\ (y , z) ->
    y $| rev-fn1 |$ (\ w
  -> w , z)))

\ (w , z) ->
  w $| un rev-fn1 |$ \ y ->


\ x ->
  let (y , z) = rev-fn2 x
      w       = rev-fn1 y
      
-}

{-
id : {A : Set} -> A <-> A
id = MkRev (\ { x -> x })
-}

swap-rev : Nat * Nat <-> Nat * Nat
swap-rev = MkRev \ { (x , y) -> (y , x) }

swap-rev-p1 : forall x -> unapply swap-rev (apply swap-rev x) ≡ x
swap-rev-p1 x = refl

case-rev : (Nat + Nat) <-> (Nat + Nat)
case-rev = MkRev \
  { (inl x) -> inr x ;
    (inr y) -> inl y }

{-
swap-rev2 : {A B : Set} -> A * B <-> B * A
swap-rev2 = MkRev \ { (x , y) -> (y , x) }
-}
{-
example : Term
example = lam visible (abs "x"
 (def (quote _$|_|$_)
  (arg (arg-info hidden (modality relevant quantity-ω))
   (def (quote Nat') [])
   ∷
   arg (arg-info hidden (modality relevant quantity-ω))
   (def (quote _*S_)
    (arg (arg-info visible (modality relevant quantity-ω))
     (def (quote Nat') [])
     ∷
     arg (arg-info visible (modality relevant quantity-ω))
     (def (quote Nat') [])
     ∷ []))
   ∷
   arg (arg-info hidden (modality relevant quantity-ω))
   (def (quote Nat') [])
   ∷
   arg (arg-info visible (modality relevant quantity-ω)) (var 0 []) ∷
   arg (arg-info visible (modality relevant quantity-ω))
   (def (quote rev-fn2) [])
   ∷
   arg (arg-info visible (modality relevant quantity-ω))
   (pat-lam
    (clause
     (("y" ,
       arg (arg-info visible (modality relevant quantity-ω))
       (def (quote Nat') []))
      ∷
      ("z" ,
       arg (arg-info visible (modality relevant quantity-ω))
       (def (quote Nat') []))
      ∷ [])
     (arg (arg-info visible (modality relevant quantity-ω))
      (con (quote Agda.Builtin.Sigma._,_)
       (arg (arg-info visible (modality relevant quantity-ω)) (var 1) ∷
        arg (arg-info visible (modality relevant quantity-ω)) (var 0) ∷
        []))
      ∷ [])
     (def (quote _$|_|$_)
      (arg (arg-info hidden (modality relevant quantity-ω))
       (def (quote Nat') [])
       ∷
       arg (arg-info hidden (modality relevant quantity-ω))
       (def (quote Nat') [])
       ∷
       arg (arg-info hidden (modality relevant quantity-ω))
       (def (quote Nat') [])
       ∷
       arg (arg-info visible (modality relevant quantity-ω)) (var 1 []) ∷
       arg (arg-info visible (modality relevant quantity-ω))
       (def (quote rev-fn1) [])
       ∷
       arg (arg-info visible (modality relevant quantity-ω))
       (pat-lam
        (clause
         (("w" ,
           arg (arg-info visible (modality relevant quantity-ω))
           (def (quote Nat') []))
          ∷ [])
         (arg (arg-info visible (modality relevant quantity-ω)) (var 0) ∷
          [])
         (def (quote _$|_|$_)
          (arg (arg-info hidden (modality relevant quantity-ω))
           (def (quote _*S_)
            (arg (arg-info visible (modality relevant quantity-ω))
             (def (quote Nat') [])
             ∷
             arg (arg-info visible (modality relevant quantity-ω))
             (def (quote Nat') [])
             ∷ []))
           ∷
           arg (arg-info hidden (modality relevant quantity-ω))
           (def (quote Nat') [])
           ∷
           arg (arg-info hidden (modality relevant quantity-ω))
           (def (quote Nat') [])
           ∷
           arg (arg-info visible (modality relevant quantity-ω))
           (con (quote (_,_))
            (arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
             arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
             arg (arg-info visible (modality relevant quantity-ω)) (var 1 []) ∷
             arg (arg-info visible (modality relevant quantity-ω)) (var 0 []) ∷
             []))
           ∷
           arg (arg-info visible (modality relevant quantity-ω))
           (def (quote rev-fn3) [])
           ∷
           arg (arg-info visible (modality relevant quantity-ω))
           (pat-lam
            (clause
             (("h" ,
               arg (arg-info visible (modality relevant quantity-ω))
               (def (quote Nat') []))
              ∷ [])
             (arg (arg-info visible (modality relevant quantity-ω)) (var 0) ∷
              [])
             (var 0 [])
             ∷ [])
            [])
           ∷ []))
         ∷ [])
        [])
       ∷ []))
     ∷ [])
    [])
   ∷ [])))
-}
