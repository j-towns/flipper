open import Prelude hiding (abs)

open import Agda.Builtin.List
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_; _*_ to _*N_; _-_ to _-N_; _<_ to _<N_)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Bool

open import Builtin.Reflection

open import Util


 -- We define a new term which uses a representation of variables that
 -- makes reversal straightforward.
data Var : Set where
   -- Non 'reversible' variables are referred to by De Bruijn index
  inner-db outer-db : Nat -> Var

   -- Reversible variables are referred to by name
  rev : String -> Var

data Term'    : Set
data Sort'    : Set
data Pattern' : Set
data Clause'  : Set
Type' = Term'

data Term' where
  var       : (x : Var)  (args : List (Arg (Term'))) → Term'
  con       : (c : Name) (args : List (Arg (Term'))) → Term'
  def       : (f : Name) (args : List (Arg (Term'))) → Term'
  lam       : (v : Visibility) (t : Abs (Term')) → Term'
  pat-lam   : (cs : List (Clause')) (args : List (Arg (Term'))) → Term'
  pi        : (a : Arg (Type')) (b : Abs (Type')) → Term'
  agda-sort : (s : Sort') → Term'
  lit       : (l : Literal) → Term'
  meta      : (x : Meta) → List (Arg (Term')) → Term'
  unknown   : Term'

data Sort' where
  set     : (t : Term') → Sort'
  lit     : (n : Nat) → Sort'
  prop    : (t : Term') → Sort'
  propLit : (n : Nat) → Sort'
  inf     : (n : Nat) → Sort'
  unknown : Sort'

data Pattern' where
  con    : (c : Name) (ps : List (Arg (Pattern'))) → Pattern'
  dot    : (t : Term') → Pattern'
  var    : (x : Var)      → Pattern'
  lit    : (l : Literal)  → Pattern'
  proj   : (f : Name)     → Pattern'
  absurd : (x : Var)      → Pattern'  -- absurd patterns count as variables

data Clause' where
  clause        : (tel : List (Σ String λ _ → Arg (Type'))) (ps : List (Arg (Pattern')))
    (t : Term') → Clause'
  absurd-clause : (tel : List (Σ String λ _ → Arg (Type'))) (ps : List (Arg (Pattern'))) → Clause'

data Quant : Set where
  qzero qone : Quant

Context : Set
Context = SnocList String

C-lookup : Context -> String -> TC Nat
C-lookup [] v = typeErrorS $ "Couldn't find name " & v & " in context."
C-lookup (ctx -, nm) v with str-eq nm v
... | false = return ∘ suc =<< (C-lookup ctx v)
... | true  = return zero

 -- The right branch denotes hidden variables, uses of which should be
 -- replaced by `unknown`
QContext : Set
QContext = SnocList (Quant × String ⊎ One)

QC-index : QContext -> Nat -> TC (String ⊎ One)
QC-index []                         i       = typeErrorS "Invalid variable lookup." -- this should be unreachable
QC-index (ctx -, left (qzero , nm)) zero    = typeErrorS $ "Reference to used variable " & nm & "."
QC-index (ctx -, left (qone ,  nm)) zero    = return (left nm)
QC-index (ctx -, right <>)          zero    = return (right <>)
QC-index (ctx -, _)                 (suc i) = QC-index ctx i

QC-use : QContext -> Nat -> TC (QContext × String)
QC-use []                         i    = typeErrorS "Invalid variable lookup." -- this should be unreachable
QC-use (ctx -, left (qzero , nm)) zero = typeErrorS $ "Attempt to re-use used variable " & nm & ". "
QC-use (ctx -, left (qone  , nm)) zero = return ((ctx -, left (qzero , nm)) , nm)
QC-use (ctx -, right <>)          zero = typeErrorS "Attempt to use hidden variable."
QC-use (ctx -, x) (suc i) = do
  ctx , nmty <- QC-use ctx i
  return $ (ctx -, x) , nmty

Term-to-Term' : QContext -> Term -> TC Term'
Term-to-Term' ctx = helper zero
  where
  convert-var : (depth : Nat) -> (x : Nat) -> TC (Var ⊎ One)
  convert-var depth x with x <N depth
  convert-var depth x | false with x <N depth +N (slist-length ctx)
  convert-var depth x | false | false = 
    return (left (outer-db (x -N (depth +N (slist-length ctx)))))
  convert-var depth x | false | true = 
    bindTC (QC-index ctx (x -N depth)) \
      { (left nm) -> return (left (rev nm))
      ; (right <>)       -> return (right <>) }
  convert-var depth x | true = return (left (inner-db x))

  args-helper : Nat -> List (Arg Term) -> TC (List (Arg Term'))
  clauses-helper : Nat -> List Clause -> TC (List Clause')
  patterns-helper : Nat -> List (Arg Pattern) -> TC (List (Arg Pattern'))
  tel-helper : Nat -> List (String × Arg Type) -> TC (List (String × Arg Type'))
  helper : Nat -> Term -> TC Term'
  
  helper depth (var x args) =
    bindTC (convert-var depth x) \
      { (left x) ->
          bindTC (args-helper depth args) \ args ->
          return (var x args)
      ; (right <>) -> return unknown }
  helper depth (con c args) =
    bindTC (args-helper depth args) \ args ->
    return (con c args)
  helper depth (def f args) =
    bindTC (args-helper depth args) \ args ->
    return (def f args)
  helper depth (lam v (abs s t)) =
    bindTC (helper (suc depth) t) \ t ->
    return (lam v (abs s t))
  helper depth (pat-lam cs args) = 
    bindTC (clauses-helper depth cs) \ cs ->
    bindTC (args-helper depth args) \ args ->
    return (pat-lam cs args)
  helper depth (pi (arg i a) (abs s b)) = 
    bindTC   (helper depth a)         \ a ->
    bindTC   (helper (suc depth) b)   \ b ->
    return (pi (arg i a) (abs s b))
  helper depth (agda-sort (set t))     = 
    bindTC (helper depth t) \ t ->
    return (agda-sort (set t))
  helper depth (agda-sort (lit n))     = return (agda-sort (lit n))
  helper depth (agda-sort (prop t))    = 
    bindTC (helper depth t) \ t ->
    return (agda-sort (prop t))
  helper depth (agda-sort (propLit n)) = return (agda-sort (propLit n))
  helper depth (agda-sort (inf n))     = return (agda-sort (inf n))
  helper depth (agda-sort unknown)     = return (agda-sort unknown)
  helper depth (lit l) = return (lit l)
   -- Sometimes the arguments to metavariables contain used
   -- variables which are not actually needed. Where this happens
   -- we attempt to solve the metavariable and retry.
  helper depth (meta x args) = 
    catchTC
      (bindTC (args-helper depth args) \ args -> return (meta x args))
      (blockOnMeta x)
  helper depth unknown = return (unknown)
  
  args-helper depth [] = return []
  args-helper depth (arg i t ∷ args) = 
    bindTC (helper depth t) \ t -> 
    bindTC (args-helper depth args) \ rest ->
    return (arg i t ∷ rest)

  clauses-helper depth [] = return []
  clauses-helper depth (clause tel ps t ∷ clauses) =
    bindTC (tel-helper depth tel) \ tel ->
    let depth = depth +N (length tel) in
    bindTC (patterns-helper depth ps) \ ps ->
    bindTC (helper depth t) \ t ->
    bindTC (clauses-helper depth clauses) \ clauses ->
    return (clause tel ps t ∷ clauses)
  clauses-helper depth (absurd-clause tel ps ∷ clauses) = 
    bindTC (tel-helper depth tel) \ tel ->
    let depth = depth +N (length tel) in
    bindTC (patterns-helper depth ps) \ ps ->
    bindTC (clauses-helper depth clauses) \ clauses ->
    return (absurd-clause tel ps ∷ clauses)

  patterns-helper depth [] = return []
  patterns-helper depth (arg i p ∷ ps) = 
    bindTC (Pattern-to-Pattern' p) \ p ->
    bindTC (patterns-helper depth ps) \ ps ->
    return (arg i p ∷ ps) 
    where
    Pattern-to-Pattern' : Pattern -> TC Pattern'
    Pattern-to-Pattern' (con c ps) = 
      bindTC (patterns-helper depth ps) \ ps ->
      return (con c ps)
    Pattern-to-Pattern' (dot t) = 
      bindTC (helper depth t) \ t ->
      return (dot t)
    Pattern-to-Pattern' (var x) = 
      bindTC (convert-var depth x) \
        { (left x) -> return (var x)
         -- Pretty sure this is unreachable, since pattern variables only refer to the
         -- telescope of the clause in which they are introduced.
        ; (right <>) -> typeError (strErr "Reference to hidden var in pattern." ∷ [])  }
    Pattern-to-Pattern' (lit l) = return (lit l)
    Pattern-to-Pattern' (proj f) = return (proj f)
    Pattern-to-Pattern' (absurd x) = 
      bindTC (convert-var depth x) \
        { (left x)  -> return (absurd x)
         -- Pretty sure this is unreachable, same reason as above.
        ; (right <>) -> typeError (strErr "Reference to hidden var in pattern." ∷ [])  }

  tel-helper depth [] = return []
  tel-helper depth ((nm , arg i ty) ∷ tel) = 
    bindTC (helper depth ty) \ ty ->
    bindTC (tel-helper (suc depth) tel) \ tel ->
    return ((nm , arg i ty) ∷ tel)

Term'-to-Term : Context -> Term' -> TC Term
Term'-to-Term ctx = helper zero
  where
  helper : Nat -> Term' -> TC Term
  args-helper : Nat -> List (Arg Term') -> TC (List (Arg Term))
  convert-var : Nat -> (v : Var) -> TC Nat
  convert-var _ (inner-db x) = return x
  convert-var depth (outer-db x) = return (depth +N (slist-length ctx) +N x)
  convert-var depth (rev nm) = 
    bindTC (C-lookup ctx nm) \ x -> 
    return (depth +N x)
  helper depth (var x args) = 
    bindTC (convert-var depth x) \ x ->
    bindTC (args-helper depth args) \ args ->
    return (var x args)
  helper depth (con c args) = 
    bindTC (args-helper depth args) \ args ->
    return (con c args)
  helper depth (def f args) = 
    bindTC (args-helper depth args) \ args ->
    return (def f args)
  helper depth (lam v (abs s t)) = 
    bindTC (helper (suc depth) t) \ t ->
    return (lam v (abs s t))
  helper depth (pat-lam cs args) = 
    bindTC (clauses-helper depth cs) \ cs ->
    bindTC (args-helper depth args) \ args ->
    return (pat-lam cs args)
    where
    clauses-helper : Nat -> List Clause' -> TC (List Clause)
    tel-helper : Nat -> List (String × Arg Type') -> TC (List (String × Arg Type))
    patterns-helper : Nat -> List (Arg Pattern') -> TC (List (Arg Pattern))
    clauses-helper depth [] = return []
    clauses-helper depth (clause tel ps t ∷ clauses) =
      bindTC (tel-helper depth tel) \ tel ->
      let depth = depth +N (length tel) in
      bindTC (patterns-helper depth ps) \ ps ->
      bindTC (helper depth t) \ t ->
      bindTC (clauses-helper depth clauses) \ clauses ->
      return (clause tel ps t ∷ clauses)
    clauses-helper depth (absurd-clause tel ps ∷ clauses) = 
      bindTC (tel-helper depth tel) \ tel ->
      let depth = depth +N (length tel) in
      bindTC (patterns-helper depth ps) \ ps ->
      bindTC (clauses-helper depth clauses) \ clauses ->
      return (absurd-clause tel ps ∷ clauses)

    tel-helper depth [] = return []
    tel-helper depth ((nm , arg i ty) ∷ tel) = 
      bindTC (helper depth ty) \ ty ->
      bindTC (tel-helper (suc depth) tel) \ tel ->
      return ((nm , arg i ty) ∷ tel) 

    patterns-helper depth [] = return []
    patterns-helper depth (arg i p ∷ ps) = 
      bindTC (Pattern'-to-Pattern p) \ p ->
      bindTC (patterns-helper depth ps) \ ps ->
      return (arg i p ∷ ps) 
      where
      Pattern'-to-Pattern : Pattern' -> TC Pattern
      Pattern'-to-Pattern (con c ps) = 
        bindTC (patterns-helper depth ps) \ ps ->
        return (con c ps)
      Pattern'-to-Pattern (dot t) = 
        bindTC (helper depth t) \ t ->
        return (dot t)
      Pattern'-to-Pattern (var x) = 
        bindTC (convert-var depth x) \ x ->
        return (var x)
      Pattern'-to-Pattern (lit l) = return (lit l)
      Pattern'-to-Pattern (proj f) = return (proj f)
      Pattern'-to-Pattern (absurd x) = 
        bindTC (convert-var depth x) \ x ->
        return (absurd x)

  helper depth (pi (arg i a) (abs s b)) = 
    bindTC (helper depth a) \ a ->
    bindTC (helper (suc depth) b) \ b ->
    return (pi (arg i a) (abs s b))
  helper depth (agda-sort (set t)) = 
    bindTC (helper depth t) \ t ->
    return (agda-sort (set t))
  helper depth (agda-sort (lit n)) = return (agda-sort (lit n))
  helper depth (agda-sort (prop t)) = 
    bindTC (helper depth t) \ t ->
    return (agda-sort (prop t))
  helper depth (agda-sort (propLit n)) = return (agda-sort (propLit n))
  helper depth (agda-sort (inf n)) = return (agda-sort (inf n))
  helper depth (agda-sort unknown) = return (agda-sort unknown)
  helper depth (lit l) = return (lit l)
  helper depth (meta x args) = 
    bindTC (args-helper depth args) \ args ->
    return (meta x args)
  helper depth unknown = return unknown

  args-helper depth [] = return []
  args-helper depth (arg i t ∷ args) = 
    bindTC (helper depth t) \ t ->
    bindTC (args-helper depth args) \ args ->
    return (arg i t ∷ args)
