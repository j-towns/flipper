open import Prelude

open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Agda.Builtin.Reflection


pattern default-modality = modality relevant quantity-ω
pattern zero-modality = modality relevant quantity-0

 -- In various places varg is the only type of arg we support
pattern varg x = arg (arg-info visible   default-modality) x
pattern harg x = arg (arg-info hidden    _               ) x
pattern iarg x = arg (arg-info instance′ _               ) x

is-visible : {A : Set} -> Arg A -> Bool
is-visible (varg _) = true
is-visible _ = false

str-eq : String -> String -> Bool
str-eq = primStringEquality

_⊎_ : (A B : Set) -> Set
A ⊎ B = Either A B

infixr 2 _⊎_

record One : Set where
  constructor <>

data Zero : Set where

data SnocList (A : Set) : Set where
  [] : SnocList A
  _-,_ : SnocList A -> A -> SnocList A

 -- TODO: Import these list functions from somewhere else...

list-reverse : {A : Set} -> List A -> SnocList A
list-reverse = go []
  where go : {A : Set} -> SnocList A -> List A -> SnocList A
        go acc [] = acc
        go acc (a ∷ as) = go (acc -, a) as

slist-index : {A : Set} -> Nat -> SnocList A -> TC A
slist-index _       []        = typeError (strErr "List index error" ∷ [])
slist-index zero    (_ -, a)  = returnTC a
slist-index (suc n) (as -, _) = slist-index n as

slist-length : {A : Set} -> SnocList A -> Nat
slist-length [] = zero
slist-length (as -, _) = suc (slist-length as)

 -- From https://hackage.haskell.org/package/base-4.16.2.0/docs/src/Data.Foldable.html#foldlM
foldlM : {A B : Set}{M : Set -> Set}{{_ : Monad M}} -> (B -> A -> M B) -> B -> List A -> M B
foldlM f z0 xs = foldr (\ { x k z -> f z x >>= k }) return xs z0
