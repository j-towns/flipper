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
QC-index ctx n with slist-index ctx n
... | just (vv qzero nm) =
  typeErrorS $ "Reference to used variable " & nm & "."
... | just (vv qone  nm) = return $ left nm
... | just hv            = return $ right <>
... | nothing            =
  typeErrorS "Internal Flipper error: invalid de Bruijn index."

QC-use : QContext -> Nat -> TC (QContext × String)
QC-use []                   i       = typeErrorS "Invalid variable lookup." -- this should be unreachable
QC-use (ctx -, vv qzero nm) zero    = typeErrorS $ "Attempt to re-use used variable " & nm & "."
QC-use (ctx -, vv qone  nm) zero    = return ((ctx -, vv qzero nm) , nm)
QC-use (ctx -, hv)          zero    = typeErrorS "Attempt to use hidden variable."
QC-use (ctx -, x)           (suc i) = do
  ctx , nmty <- QC-use ctx i
  return $ (ctx -, x) , nmty

QC-use' : QContext -> String -> TC (QContext × Nat)
QC-use' [] v = typeErrorS $ "Couldn't find name " & v & " in context."
QC-use' (ctx -, vv qzero nm) v = if nm ==? v
  then typeErrorS $ "Internal Flipper error."  -- should be unreachable
  else QC-use' ctx v >>= \ (ctx , x) -> return ((ctx -, hv) , (suc x))
QC-use' (ctx -, vv qone  nm) v = if nm ==? v
  then return ((ctx -, vv qzero nm) , zero)
  else QC-use' ctx v >>= \ (ctx , x) -> return ((ctx -, vv qone nm) , suc x)
QC-use' (ctx -, hv) v = QC-use' ctx v >>= \ (ctx , x) -> return ((ctx -, hv) , (suc x))

QC-lookup : QContext -> String -> TC Nat
QC-lookup ctx nm = fmap snd $ QC-use' ctx nm

VarSet = SnocList String

QC-to-VarSet : QContext -> VarSet
QC-to-VarSet = slist-concatMap \ { (vv qzero _) → []
                                 ; (vv qone nm) → [] -, nm
                                 ; hv           → []
                                 }

VarSet-lookup : VarSet -> String -> TC Nat
VarSet-lookup []          v =
  typeErrorS $ "Couldn't find name " & v & " in VarSet."
VarSet-lookup (ctx -, nm) v = if nm ==? v
  then return zero
  else return ∘ suc =<< (VarSet-lookup ctx v)

pattern packed-fn tel ps t = pat-lam (clause tel ps t ∷ []) []

{-# TERMINATING #-}
pack-vars : QContext -> VarSet -> Term -> TC Term
pack-vars ctx vars = pack zero
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

pack-vars-lam-wrap : QContext -> Term -> TC (VarSet × Term)
pack-vars-lam-wrap ctx t = do
  let vars = QC-to-VarSet ctx
  t <- pack-vars ctx vars t
  let vars-ls = slist-to-list vars
  let num-vars = length vars-ls
  return $ vars ,
    (packed-fn (zip vars-ls (replicate num-vars (vArg unknown)))
    (mk-ps num-vars) t)
  where
  mk-ps : Nat -> List (Arg Pattern)
  mk-ps n = map (vArg ∘ var) (reverse (from 0 for n))
