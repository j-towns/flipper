open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Agda.Builtin.Reflection


pattern default-modality = modality relevant quantity-ω

 -- In various places varg is the only type of arg we support
pattern varg x = arg (arg-info visible   default-modality) x
pattern harg x = arg (arg-info hidden    default-modality) x
pattern iarg x = arg (arg-info instance′ default-modality) x

str-eq : String -> String -> Bool
str-eq = primStringEquality

data _+_ (A B : Set) : Set where
 inl : A -> (A + B)
 inr : B -> (A + B)

_*_ : Set -> Set -> Set
A * B = Σ A \ _ -> B

infixr 4 _+_
infixr 5 _*_

record One : Set where
  constructor <>

data Zero : Set where

data SnocList (A : Set) : Set where
  [] : SnocList A
  _-,_ : SnocList A -> A -> SnocList A

 -- TODO: Import these list functions from somewhere else...
list-map : {A B : Set} -> (A -> B) -> List A -> List B
list-map f [] = []
list-map f (a ∷ as) = f a ∷ (list-map f as)

list-reverse : {A : Set} -> List A -> SnocList A
list-reverse = go []
  where go : {A : Set} -> SnocList A -> List A -> SnocList A
        go acc [] = acc
        go acc (a ∷ as) = go (acc -, a) as

list-reverse' : {A : Set} -> List A -> List A
list-reverse' = go []
  where go : {A : Set} -> List A -> List A -> List A
        go acc [] = acc
        go acc (a ∷ as) = go (a ∷ acc) as

slist-index : {A : Set} -> Nat -> SnocList A -> TC A
slist-index _       []        = typeError (strErr "List index error" ∷ [])
slist-index zero    (_ -, a)  = returnTC a
slist-index (suc n) (as -, _) = slist-index n as

list-concat : {A : Set} -> List (List A) -> List A
list-concat [] = []
list-concat ([] ∷ ass) = list-concat ass
list-concat ((a ∷ as) ∷ ass) = a ∷ list-concat (as ∷ ass)

list-length : {A : Set} -> List A -> Nat
list-length [] = zero
list-length (_ ∷ as) = suc (list-length as)

slist-length : {A : Set} -> SnocList A -> Nat
slist-length [] = zero
slist-length (as -, _) = suc (slist-length as)

mapTC : {A B : Set} -> (A -> TC B) -> List A -> TC (List B)
mapTC f [] = returnTC []
mapTC f (a ∷ as) = bindTC (f a) \ b ->
                   bindTC (mapTC f as) \ bs ->
                   returnTC (b ∷ bs)
