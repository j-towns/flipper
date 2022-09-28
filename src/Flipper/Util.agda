module Flipper.Util where

open import Prelude

open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Builtin.Reflection


pattern default-modality = modality relevant quantity-ω

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

slist-index : {A : Set} -> SnocList A -> Nat -> Maybe A
slist-index []        _       = nothing
slist-index (_  -, a) zero    = just a
slist-index (as -, _) (suc n) = slist-index as n

slist-length : {A : Set} -> SnocList A -> Nat
slist-length [] = zero
slist-length (as -, _) = suc (slist-length as)

slist-map : {A B : Set} -> (A -> B) -> SnocList A -> SnocList B
slist-map f [] = []
slist-map f (as -, a) = slist-map f as -, f a

slist-foldl : {A B : Set} -> (B -> A -> B) -> B -> SnocList A -> B
slist-foldl f b []        = b
slist-foldl f b (as -, a) = f (slist-foldl f b as) a

slist-foldr : {A B : Set} -> (A -> B -> B) -> B -> SnocList A -> B
slist-foldr f b [] = b
slist-foldr f b (as -, a) = slist-foldr f (f a b) as

_++S'_ : forall {A} -> SnocList A -> SnocList A -> SnocList A
_++S'_ = slist-foldl _-,_

slist-to-list : forall {A} -> SnocList A -> List A
slist-to-list = slist-foldr _∷_ []

slist-concat : {A : Set} -> SnocList (SnocList A) -> SnocList A
slist-concat = slist-foldl _++S'_ []

slist-concatMap : {A B : Set} -> (A -> SnocList B) -> SnocList A -> SnocList B
slist-concatMap f = slist-concat ∘ slist-map f

private
  reverse-cumsum' : forall {n} -> Vec Nat n -> Vec Nat n
  reverse-cumsum' []           = []
  reverse-cumsum' (_ ∷ [])     = 0 ∷ []
  reverse-cumsum' (_ ∷ x ∷ xs) with reverse-cumsum' (x ∷ xs)
  reverse-cumsum' (_ ∷ x ∷ xs) | (sum ∷ rest) = x + sum ∷ sum ∷ rest

reverse-cumsum : List Nat -> List Nat
reverse-cumsum = vecToList ∘ reverse-cumsum' ∘ listToVec
