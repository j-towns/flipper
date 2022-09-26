module Flipper.Util where

open import Prelude

open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Builtin.Reflection


pattern default-modality = modality relevant quantity-ω
pattern zero-modality = modality relevant quantity-0

 -- In various places varg is the only type of arg we support
pattern varg x = arg (arg-info visible   default-modality) x
pattern harg x = arg (arg-info hidden    _               ) x
pattern iarg x = arg (arg-info instance′ _               ) x

is-visible : {A : Set} -> Arg A -> Bool
is-visible (varg _) = true
is-visible _ = false

_⊎_ : (A B : Set) -> Set
A ⊎ B = Either A B

infixr 2 _⊎_

record One : Set where
  constructor <>

data Zero : Set where

data SnocList (A : Set) : Set where
  [] : SnocList A
  _-,_ : SnocList A -> A -> SnocList A

infixr 5 _++S_

_++S_ : forall {A} -> SnocList A -> List A -> SnocList A
xs ++S []       = xs
xs ++S (y ∷ ys) = (xs -, y) ++S ys

list-to-slist : {A : Set} -> List A -> SnocList A
list-to-slist = foldl _-,_ []

slist-to-list : forall {A} -> SnocList A -> List A
slist-to-list = go [] where
  go : forall {A} -> List A -> SnocList A -> List A
  go acc []        = acc
  go acc (as -, a) = go (a ∷ acc) as

slist-index : {A : Set} -> SnocList A -> Nat -> TC A
slist-index []        _       = typeErrorS "List index error"
slist-index (_  -, a) zero    = return a
slist-index (as -, _) (suc n) = slist-index as n

slist-length : {A : Set} -> SnocList A -> Nat
slist-length [] = zero
slist-length (as -, _) = suc (slist-length as)
