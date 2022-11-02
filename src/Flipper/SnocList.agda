module Flipper.SnocList where

open import Prelude

open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Builtin.Reflection


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
