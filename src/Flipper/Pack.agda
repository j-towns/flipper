module Flipper.Pack where
 -- Utilities for lambda-abstracting the Flippables that appear in
 -- equations in an outer Flippable expression. 
 -- These need to be abstracted because otherwise they are normalized/
 -- expanded, which breaks our automatically generated proofs.
 -- Abstracting also means that we are able to move the terms, without
 -- breaking free variables' de Bruijn indices.


open import Builtin.Reflection
open import Prelude hiding (abs)
open import Flipper.Parser
open import Flipper.SnocList


private
  module Pack (ctx : QContext) where
     -- On failure we return the name of the already-used variable which
     -- was referred to.
    Pck : Set -> Set
    Pck A = Nat -> A -> Either String A
    
     -- Variables which are hidden in the context need to be replaced by
     -- `unknown`, signalled by the rightmost `unit` branch here:
    pckVar : Nat -> Nat -> Either String (Either Nat ⊤)
    pckVar = go 0 ctx where
      go : Nat -> QContext -> Nat -> Nat -> Either String (Either Nat ⊤)
      go acc ctx                  (suc depth) zero    = right (left acc)
      go acc []                   zero        zero    = right (left acc)
      go acc (ctx -, vv qzero nm) zero        zero    = left nm
      go acc (ctx -, vv qone _)   zero        zero    = right (left acc)
      go acc (ctx -, hv)          zero        zero    = right (right unit)
      go acc []                   zero        (suc x) = go (suc acc) [] zero x
      go acc (ctx -, vv qzero _)  zero        (suc x) = go acc ctx zero x
      go acc (ctx -, vv qone  _)  zero        (suc x) = go (suc acc) ctx zero x
      go acc (ctx -, hv)          zero        (suc x) = go acc ctx zero x
      go acc ctx                  (suc depth) (suc x) = go (suc acc) ctx depth x
    
    pck        : Pck Term
    pckArgs    : Pck (List (Arg Term))
    pckArg     : Pck (Arg Term)
    pckAbs     : Pck (Abs Term)
    pckClauses : Pck (List Clause)
    pckClause  : Pck Clause
    pckSort    : Pck Sort
    pckTel     : Pck Telescope
    pckPats    : Pck (List (Arg Pattern))
    pckPatArg  : Pck (Arg Pattern)
    pckPat     : Pck Pattern
    
    pck d (var x args) with pckVar d x
    ... | left nm            = left nm
    ... | right (left  x)    = var x <$> pckArgs d args
    ... | right (right unit) = pure unknown
    pck d (con c args)       = con c <$> pckArgs d args
    pck d (def f args)       = def f <$> pckArgs d args
    pck d (lam v t)          = lam v <$> pckAbs d t
    pck d (pat-lam cs args)  = pat-lam <$> pckClauses d cs <*> pckArgs d args
    pck d (pi a b)           = pi <$> pckArg d a <*> pckAbs d b
    pck d (agda-sort s)      = agda-sort <$> pckSort d s
    pck d (lit l)            = pure (lit l)
    pck d (meta m args)      = meta m <$> pckArgs d args
    pck d unknown            = pure unknown
    
    pckArgs    d []          = pure []
    pckArgs    d (a ∷ args)  = _∷_ <$> pckArg d a <*> pckArgs d args
    pckArg     d (arg i x)   = arg i <$> pck d x
    pckAbs     d (abs s x)   = abs s <$> pck (suc d) x
    pckSort    d (set t)     = set <$> pck d t
    pckSort    d (lit n)     = pure (lit n)
    pckSort    d (prop t)    = prop <$> pck d t
    pckSort    d (propLit n) = pure (propLit n)
    pckSort    d (inf n)     = pure (inf n)
    pckSort    d unknown     = pure unknown
    
    pckClauses d []         = pure []
    pckClauses d (x ∷ cs)   = _∷_ <$> pckClause d x <*> pckClauses d cs
    
    pckClause d (clause tel ps t) = clause <$> pckTel d tel <*> pckPats d ps <*> pck (suc d) t
    pckClause d (absurd-clause tel ps) = absurd-clause <$> pckTel d tel <*> pckPats d ps
    
    pckTel d []                 = pure []
    pckTel d ((nm , aty) ∷ tel) = _∷_ <$> (nm ,_ <$> pckArg d aty) <*> pckTel (suc d) tel
    
    pckPats d []       = pure []
    pckPats d (p ∷ ps) = _∷_ <$> pckPatArg d p <*> pckPats d ps
    
    pckPat d (con c ps) = con c <$> pckPats d ps
    pckPat d (dot t)    = dot <$> pck d t
    pckPat d (var x)    = pure (var x)
    pckPat d (lit l)    = pure (lit l)
    pckPat d (proj f)   = pure (proj f)
    pckPat d (absurd x) = pure (absurd x)
    
    pckPatArg d (arg i p) = arg i <$> pckPat d p
    
    pack : Term -> Either String Term
    pack = pck 0
  open Pack
  
  wrapAbs : (String -> Term -> Term) -> Term -> VarSet -> Term
  wrapAbs = slist-foldr

packLamWrap : Term -> QCParser Term
packLamWrap t ctx with pack ctx t
... | left nm = right (strErr ("Reference to used variable " & nm & ".") ∷ [])
... | right t =
  left (ctx , wrapAbs (\ { nm t -> lam visible (abs nm t) }) t (QC-to-VarSet ctx))

packPiWrap : Type -> QCParser Type
packPiWrap ty ctx with pack ctx ty
... | left nm  = right (strErr ("Reference to used variable " & nm & " in type.") ∷ [])
... | right ty =
  left (ctx , wrapAbs (\ { nm ty -> pi (vArg unknown) (abs nm ty) }) ty (QC-to-VarSet ctx))

