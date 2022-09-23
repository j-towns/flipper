module Flipper.Term where

open import Prelude hiding (abs)
open import Container.Traversable

open import Agda.Builtin.List
open import Agda.Builtin.Nat using (Nat; zero; suc)
  renaming (_+_ to _+N_; _*_ to _*N_; _-_ to _-N_; _<_ to _<N_)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Bool

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

QC-index : QContext -> Nat -> TC (String ⊎ One)
QC-index []                   i       = typeErrorS "Invalid variable lookup." -- this should be unreachable
QC-index (ctx -, vv qzero nm) zero    = typeErrorS $ "Reference to used variable " & nm & "."
QC-index (ctx -, vv qone  nm) zero    = return (left nm)
QC-index (ctx -, hv)          zero    = return (right <>)
QC-index (ctx -, _)           (suc i) = QC-index ctx i

QC-use : QContext -> Nat -> TC (QContext × String)
QC-use []                   i       = typeErrorS "Invalid variable lookup." -- this should be unreachable
QC-use (ctx -, vv qzero nm) zero    = typeErrorS $ "Attempt to re-use used variable " & nm & ". "
QC-use (ctx -, vv qone  nm) zero    = return ((ctx -, vv qzero nm) , nm)
QC-use (ctx -, hv)          zero    = typeErrorS "Attempt to use hidden variable."
QC-use (ctx -, x)           (suc i) = do
  ctx , nmty <- QC-use ctx i
  return $ (ctx -, x) , nmty

QC-lookup : QContext -> String -> TC (QContext × Nat)
QC-lookup [] v = typeErrorS $ "Couldn't find name " & v & " in context."
QC-lookup (ctx -, vv qzero nm) v = typeErrorS $ "Internal Flipper error." -- should be unreachable
QC-lookup (ctx -, vv qone  nm) v = if str-eq nm v
  then return ((ctx -, vv qzero nm) , zero)
  else QC-lookup ctx v >>= \ (ctx , x) -> return ((ctx -, vv qone nm) , suc x)
QC-lookup (ctx -, hv) v = QC-lookup ctx v >>= \ (ctx , x) -> return ((ctx -, hv) , (suc x))

QC-lookup' : QContext -> String -> TC Nat
QC-lookup' ctx nm = fmap snd $ QC-lookup ctx nm

 -- Based on https://github.com/UlfNorell/agda-prelude/blob/3d143d/src/Tactic/Reflection/Free.agda
 -- We use this to keep track of all the variables which are in scope
 -- in a Flippable.
VarSet = SnocList String  -- ordered

 -- disjoint union (error on duplicate)
_∪_ : VarSet → VarSet → TC VarSet
[]        ∪ ys        = return ys
xs        ∪ []        = return xs
(xs -, x) ∪ (ys -, y) =
  case-cmp compare x y
    less    _ => return ∘ (_-, y) =<< (xs -, x) ∪ ys
    equal   _ => typeErrorS
      "Shadowed names are not allowed in Flippables."
    greater _ => return ∘ (_-, x) =<< xs ∪ (ys -, y)

_setminus_ : VarSet -> VarSet -> TC VarSet
xs       setminus []         = return xs
[]       setminus (_ -, _ )  = typeErrorS
  "Subtracting non-empty from empty set"
(xs -, x) setminus (ys -, y) = 
  case-cmp compare x y
    less    _ => typeErrorS
      "Subtracted set not contained in left-hand-side."
    equal   _ => xs setminus ys
    greater _ => return ∘ (_-, x) =<< xs setminus (ys -, y)

∅ : VarSet
∅ = []

QC-to-VarSet : QContext -> TC VarSet
QC-to-VarSet [] = return []
QC-to-VarSet (ctx -, vv qzero _) = QC-to-VarSet ctx
QC-to-VarSet (ctx -, vv qone nm) = do
  rest <- QC-to-VarSet ctx
  all <- rest ∪ ([] -, nm)
  return all 
QC-to-VarSet (ctx -, hv)         = QC-to-VarSet ctx

VarSet-lookup : VarSet -> String -> TC Nat
VarSet-lookup [] v = typeErrorS $ "Couldn't find name " & v & " in VarSet."
VarSet-lookup (ctx -, nm) v with str-eq nm v
... | false = return ∘ suc =<< (VarSet-lookup ctx v)
... | true  = return zero

{-# TERMINATING #-}
pack-vars' : QContext -> VarSet -> Term -> TC Term
pack-vars' ctx vars = pack zero
  where
  ctx-len = slist-length ctx
  vars-len = slist-length vars
  
  pack-var : (depth : Nat) -> (x : Nat) -> TC (Nat ⊎ One)
  pack-var depth x with x <N depth
  pack-var depth x | false with x <N depth +N (slist-length ctx)
  pack-var depth x | false | false = return (left (x +N vars-len -N ctx-len))
  pack-var depth x | false | true  = 
    QC-index ctx (x -N depth) >>=
    \ { (left  nm) -> VarSet-lookup vars nm >>= \ i -> return (left (i +N depth))
      ; (right <>) -> return (right <>) } 
  pack-var depth x | true = return (left x)

  pack : Nat -> Term -> TC Term
  pack-args : Nat -> List (Arg Term) -> TC (List (Arg Term))
  pack-clause : Nat -> Clause -> TC Clause
  pack-patterns : Nat -> List (Arg Pattern) -> TC (List (Arg Pattern))
  pack-tel : Nat -> List (String × Arg Type) -> TC (List (String × Arg Type))

  pack depth (var x args) =
    pack-var depth x >>= \
      { (left  x)  -> return ∘ var x =<< pack-args depth args
      ; (right <>) -> return unknown }
  pack depth (con c args) = return ∘ con c =<< pack-args depth args
  pack depth (def f args) = return ∘ def f =<< pack-args depth args
  pack depth (lam v (abs s t)) =
    pack (suc depth) t >>= \ t ->
    return (lam v (abs s t))
  pack depth (pat-lam cs args) = 
    traverse (pack-clause depth) cs >>= \ cs ->
    pack-args depth args >>= \ args ->
    return (pat-lam cs args)
  pack depth (pi (arg i a) (abs s b)) = 
    pack depth a >>=         \ a ->
    pack (suc depth) b >>=   \ b ->
    return (pi (arg i a) (abs s b))
  pack depth (agda-sort (set t))     = 
    pack depth t >>= \ t ->
    return (agda-sort (set t))
  pack depth (agda-sort (prop t))    = 
    pack depth t >>= \ t ->
    return (agda-sort (prop t))
   -- Sometimes the arguments to metavariables contain used
   -- variables which are not actually needed. Where this happens
   -- we attempt to solve the metavariable and retry.
  pack depth (meta x args) = 
    catchTC
      (pack-args depth args >>= \ args -> return (meta x args))
      (blockOnMeta x)
  pack depth t     = return t
  
  pack-args depth = traverse $ traverse $ pack depth

  pack-clause depth (clause tel ps t) = do
    tel <- pack-tel depth tel
    let depth = depth +N (length tel)
    ps <- pack-patterns depth ps
    t <- pack depth t
    return (clause tel ps t)
  pack-clause depth (absurd-clause tel ps) = do
    tel <- pack-tel depth tel
    let depth = depth +N (length tel)
    ps <- pack-patterns depth ps
    return (absurd-clause tel ps)

  pack-patterns depth = traverse $ traverse pack-pattern
    where
    pack-pattern : Pattern -> TC Pattern
    pack-pattern (dot t) = return ∘ dot =<< pack depth t
    pack-pattern p = return p

  pack-tel depth [] = return []
  pack-tel depth ((nm , arg i ty) ∷ tel) = do
    ty <- pack depth ty
    tel <- pack-tel (suc depth) tel
    return ((nm , arg i ty) ∷ tel)

pack-vars : QContext -> Term -> TC Term
pack-vars ctx t = do
  vars <- QC-to-VarSet ctx
  pack-vars' ctx vars t
