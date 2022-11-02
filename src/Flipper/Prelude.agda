module Flipper.Prelude where

open import Prelude using (_≡_; refl)
open import Flipper public


id : {A : Set} -> A <-> A
id = F \ { x -> x }

_<>_ : {A B C : Set} -> (A <-> B) -> (B <-> C) -> A <-> C
f <> g = F \ { a -> a $| f |$ \ { b ->
                    b $| g |$ \ { c -> c }}}
infixl 2 _<>_

composeF : forall {A C} B -> (A <-> B) -> (B <-> C) -> A <-> C
composeF _ f g = f <> g
syntax composeF B f g = f < B > g

=F= : {A B : Set} -> A ≡ B -> A <-> B
=F= refl = F \ { x -> x}
