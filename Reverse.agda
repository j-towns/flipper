open import Agda.Builtin.Reflection
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)

open import Term
open import Util


 -- Reversible syntax
data RevPat : Set where
  con : (c : Name) (ps : List RevPat) -> RevPat
  var : (nm : String) (ty : Type') -> RevPat
   -- TODO: Add absurd

record RevFn : Set where
  pattern
  constructor MkRevFn
  field
    fn : Term'
    inty outty : Type'

record RevEqn : Set where
  pattern
  constructor MkRevEqn
  field
    argp : RevPat
    fn : RevFn
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
    inty outty : Type'

reverse : RevTerm -> RevTerm
RevTerm-to-Term : RevTerm -> TC Term
Term-to-RevTerm : Term -> (inty outty : Type) -> TC RevTerm
reverse-tactic : {A B : Set} (apply : A -> B) -> Term -> TC ⊤

record _<->_ (A B : Set) : Set where
  pattern
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
un (MkRev apply {unapply}) = MkRev unapply {apply}

_$|_|$_ : {A B C : Set} -> A -> (A <-> B) -> (B -> C) -> C
a $| f |$ g = g (apply f a)


reverse (MkRT branches inty outty) = MkRT (list-map reverse-br branches) outty inty
  where
  reverse-br : RevBranch -> RevBranch
  reverse-br (branch inp eqns outp) = branch outp (list-reverse' (list-map reverse-eqn eqns)) inp
    where
    reverse-eqn : RevEqn -> RevEqn
    reverse-eqn (MkRevEqn argp (MkRevFn fn inty outty) resp) =
      MkRevEqn resp (MkRevFn (def (quote un) (harg inty ∷ harg outty ∷ varg fn ∷ [])) outty inty) argp

reverse-tactic {inty} {outty} apply hole = 
  bindTC (quoteTC inty) \ inty ->
  bindTC (quoteTC outty) \ outty ->
  bindTC (quoteTC apply) \ term ->
  {-
  bindTC (quoteTC term) \ t ->
  typeError (termErr t ∷ [])
  -}
  bindTC (Term-to-RevTerm term inty outty) \ rt ->
  let rt = reverse rt in
  bindTC (RevTerm-to-Term rt) \ term ->
  unify hole term

  

 -- We use pattern matching on these 'ok' forms to lossily
 -- transform from Term to RevTerm. Any pattern that isn't ok
 -- will throw an error. We use the same ok patterns
 -- to reconstruct a Term from a RevTerm...
pattern ok-pat-lam cs = pat-lam cs []
pattern ok-clause tel inp term = clause tel ((varg inp) ∷ []) term
pattern ok-cons argty resty outty-global argpat rev-fn res-tel respat rest-term =
  def (quote _$|_|$_) (
          harg argty ∷
          harg resty ∷
          harg outty-global ∷
          varg argpat ∷
          varg rev-fn ∷
          varg (ok-pat-lam (ok-clause res-tel respat rest-term ∷ [])) ∷ [])

Term-to-RevTerm (ok-pat-lam cs) inty outty = 
  bindTC (mapTC process-branch cs) \ bs ->
  bindTC (Term-to-Term' [] inty) \ inty ->
  bindTC (Term-to-Term' [] outty) \ outty ->
  returnTC (MkRT bs inty outty)
  where
  process-tel : QContext -> List (String * Arg Type) -> TC QContext
  process-tel ctx [] = returnTC ctx
  process-tel ctx ((nm , varg ty) ∷ tel) = 
    bindTC (Term-to-Term' ctx ty) \ ty ->
    process-tel (ctx -, (one , nm , ty)) tel
  process-tel ctx ((nm , _) ∷ _) = typeError (strErr "Non-visible element in telescope." ∷ [])

  Pattern-to-RevPat : QContext -> Pattern -> TC RevPat
  Pattern-to-RevPat ctx (con c ps) =
    bindTC (helper ps) \ ps ->
    returnTC (con c ps)
    where
    helper : (ps : List (Arg Pattern)) -> TC (List RevPat)
    helper [] = returnTC []
    helper (varg p ∷ ps) = 
      bindTC (Pattern-to-RevPat ctx p) \ p ->
      bindTC (helper ps) \ ps ->
      returnTC (p ∷ ps)
    helper (_ ∷ ps) = helper ps -- typeError (strErr "Non-visible element in pattern." ∷ [])
  Pattern-to-RevPat ctx (var x) = 
    bindTC (QC-index ctx x) \ (nm , ty) ->
    returnTC (var nm ty)
  Pattern-to-RevPat ctx p = typeError (strErr "Patterns must either be variables or constructors" ∷ [])

  Term-to-RevPat : QContext -> Term -> TC (QContext * RevPat)
  Term-to-RevPat ctx (var x []) = 
    bindTC (QC-use ctx x) \ (ctx , nm , ty) ->
    returnTC (ctx , var nm ty)
  Term-to-RevPat ctx (con c ps) = 
    bindTC (args-helper ctx ps) \ (ctx , ps) ->
    returnTC (ctx , (con c ps))
    where
    args-helper : QContext -> List (Arg Term) -> TC (QContext * List RevPat)
    args-helper ctx [] = returnTC (ctx , [])
    args-helper ctx (harg u ∷ args) = args-helper ctx args
    -- args-helper ctx (harg _       ∷ args) =
    --  typeError (strErr "Explicitly providing implicit arguments to constructors is not supported." ∷ [])
    args-helper ctx (iarg unknown ∷ args) = args-helper ctx args
    args-helper ctx (iarg _       ∷ args) =
      typeError (strErr "Explicitly providing instance arguments to constructors is not supported." ∷ [])
    args-helper ctx (varg a ∷ args) =
      bindTC   (Term-to-RevPat ctx a) \ (ctx , a) ->
      bindTC   (args-helper ctx args) \ (ctx , args) ->
      returnTC (ctx , (a ∷ args)) 
    args-helper _ _ = typeError (strErr "Unsupported arg info in subterm." ∷ [])
  Term-to-RevPat ctx t = typeError (strErr "Argument/output must be a variable or constructor" ∷ [])
  
  process-term : QContext -> Term -> TC (List RevEqn * RevPat)
  process-term ctx (ok-cons argty resty _ argpat rev-fn res-tel respat rest-term) = 
    bindTC (Term-to-Term' ctx argty) \ argty ->
    bindTC (Term-to-Term' ctx resty) \ resty ->
    bindTC (Term-to-RevPat ctx argpat) \ (ctx , argpat) ->
    bindTC (Term-to-Term' ctx rev-fn) \ rev-fn ->
    bindTC (process-tel ctx res-tel) \ ctx ->
    bindTC (Pattern-to-RevPat ctx respat) \ respat ->
    bindTC (process-term ctx rest-term) \ (eqns , outp) ->
    returnTC ((MkRevEqn argpat (MkRevFn rev-fn argty resty) respat ∷ eqns) , outp)
  process-term ctx t = 
    bindTC (Term-to-RevPat ctx t) \ (ctx , outp) ->
     -- TODO: Check that all variables in ctx have  been used
    returnTC ([] , outp)
  
  process-branch : Clause -> TC RevBranch
  process-branch (ok-clause tel inp term) = 
    bindTC (process-tel [] tel) \ ctx ->
    bindTC (Pattern-to-RevPat ctx inp) \ inp ->
    bindTC (process-term ctx term) \ (eqns , outp) ->
    returnTC (branch inp eqns outp)
  process-branch c = typeError (strErr "Clauses must have exactly one bound pattern." ∷ [])
Term-to-RevTerm t inty outty = typeError (strErr "Only pattern-lambda terms can be reversed." ∷ [])

RevTerm-to-Term (MkRT bs inty outty) = 
  bindTC (mapTC process-branch bs) \ cs ->
  returnTC (ok-pat-lam cs)
  where
  process-tel : Context -> RevPat -> TC (Context * List (String * Arg Type))
  process-tel ctx p = helper ctx (p ∷ [])
    where
    helper : Context -> List RevPat -> TC (Context * List (String * Arg Type))
    helper ctx [] = returnTC (ctx , [])
    helper ctx (con c ps ∷ ps') = 
      bindTC (helper ctx ps) \ (ctx , tel-start) ->
      bindTC (helper ctx ps') \ (ctx , tel-end) ->
      returnTC (ctx , list-concat (tel-start ∷ tel-end ∷ []))
    helper ctx (var nm ty ∷ ps) =
      bindTC (Term'-to-Term ctx ty) \ ty ->
      let ctx = ctx -, (nm , ty) in
      bindTC (helper ctx ps) \ (ctx , tel) ->
      returnTC (ctx , (nm , varg ty) ∷ tel)

  RevPat-to-Pattern : Context -> RevPat -> TC Pattern
  RevPat-to-Pattern ctx (con c ps) = 
    bindTC (helper ps) \ ps ->
    returnTC (con c ps)
    where
    helper : List RevPat -> TC (List (Arg Pattern))
    helper [] = returnTC []
    helper (p ∷ ps) = 
      bindTC (RevPat-to-Pattern ctx p) \ p ->
      bindTC (helper ps) \ ps ->
      returnTC (varg p ∷ ps)
  RevPat-to-Pattern ctx (var nm ty) = 
    bindTC (C-lookup ctx nm) \ i ->
    returnTC (var i)

  RevPat-to-Term : Context -> RevPat -> TC Term
  RevPat-to-Term ctx (con c ps) = 
    bindTC (helper ps) \ ps ->
    returnTC (con c ps)
    where
    helper : List RevPat -> TC (List (Arg Term))
    helper [] = returnTC []
    helper (p ∷ ps) = 
      bindTC (RevPat-to-Term ctx p) \ p ->
      bindTC (helper ps) \ ps ->
      returnTC (varg p ∷ ps)
  RevPat-to-Term ctx (var nm ty) = 
    bindTC (C-lookup ctx nm) \ i ->
    returnTC (var i [])

  process-term : Context -> List RevEqn -> RevPat -> TC Term
  process-term ctx [] outp = RevPat-to-Term ctx outp
  process-term ctx (MkRevEqn argp (MkRevFn fn argty resty) resp ∷ eqns) outp = 
    bindTC (RevPat-to-Term ctx argp) \ argp ->
    bindTC (Term'-to-Term ctx fn) \ fn ->
    bindTC (Term'-to-Term ctx argty) \ argty ->
    bindTC (Term'-to-Term ctx resty) \ resty ->
    bindTC (Term'-to-Term ctx outty) \ outty ->
    bindTC (process-tel ctx resp) \ (ctx , res-tel) ->
    bindTC (RevPat-to-Pattern ctx resp) \ respat ->
    bindTC (process-term ctx eqns outp) \ rest-term ->
    returnTC ( ok-cons argty resty outty argp fn res-tel respat rest-term )

  process-branch : RevBranch -> TC Clause
  process-branch (branch inp eqns outp) =
    bindTC (process-tel [] inp) \ (ctx , tel) ->
    bindTC (RevPat-to-Pattern ctx inp) \ inp ->
    bindTC (process-term ctx eqns outp) \ term ->
    returnTC (ok-clause tel inp term)


-------------------------------------------------------------------------------------

test-id : {A : Set} -> A <-> A
test-id = MkRev (\ { x -> x })

test-pair-swp : {A B : Set} -> A * B <-> B * A
test-pair-swp = MkRev \ { (a , b) -> b , a }

test-sum-swp : {A B : Set} -> A + B <-> B + A
test-sum-swp = MkRev \ { (inl a) → inr a
                         ; (inr b) → inl b }

test-composed : Nat * Nat + Nat <-> Nat + Nat * Nat
test-composed = MkRev (
  \ { (inl (m , n)) -> 
        m $| test-id |$ \ { m' ->
        n $| test-id |$ \ { n' ->
      inr (n' , m') }}
    ; (inr x) -> inl x })
