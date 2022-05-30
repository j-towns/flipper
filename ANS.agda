{-# OPTIONS --no-forcing #-}

open import Reverse using (_<->_; MkRev; _$|_|$_; un)
open import Util

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

open _<->_

data Nat : Set where
  z : Nat
  s : Nat -> Nat

_+N_ : Nat -> Nat -> Nat
a +N z = a
a +N s b = s (a +N b)

infixr 4 _+N_

data Range : Nat -> Nat -> Set where
  z  : {b : Nat}                -> Range z     (s b)
  s1 : {b : Nat}   -> Range z b -> Range z     (s b)
  s2 : {a b : Nat} -> Range a b -> Range (s a) (s b)

{-
move : {a b : Nat} (c : Nat) -> Range a b <-> Range (a +N c) (b +N c)
move z     = MkRev \ { n ->                           n        }
move (s c) = MkRev \ { n -> n $| move c |$ \ { n+c -> s2 n+c } }
-}

data _<_ : Nat -> Nat -> Set where
  z<sn : {o : Nat}            -> z   < s o
  s<s  : {p q : Nat} -> p < q -> s p < s q

infix 1 _<_

record Range' (a b : Nat) : Set where
  constructor MkRange'
  field
    x    : Nat
    a<=x : a < s x
    x<b  : x < b

macro
  dump : {a b : Nat} -> (Range a b -> Range' a b) -> Term -> TC ⊤
  dump f hole =
    bindTC (quoteTC f) \ t ->
    {-
    bindTC (inferType hole) \ holety ->
    bindTC (checkType t holety) \ t ->
    unify hole t
    -}
    bindTC (inferType hole) \ holety ->
    bindTC (checkType t holety) \ t ->
    bindTC (quoteTC t) \ `t ->
    typeError (termErr `t ∷ [])


R-to-R' : {a b : Nat} -> Range a b <-> Range' a b
R-to-R' {a} {b} = MkRev ( ((\ { z      →                                              MkRange' z      z<sn       z<sn
                              ; (s1 x) → x $| R-to-R' |$ \ { (MkRange' x' z<sn x<b) → MkRange' (s x') z<sn       (s<s x<b) }
                              ; (s2 x) → x $| R-to-R' |$ \ { (MkRange' x' a<=x x<b) → MkRange' (s x') (s<s a<=x) (s<s x<b) } })))

{-
                            {  (\ { (MkRange' z      z<sn       z<sn)      → z
                                  ; (MkRange' (s x') z<sn       (s<s x<b)) → MkRange' x' z<sn x<b $| un R-to-R' |$ \ { x -> s1 x }
                                  ; (MkRange' (s x') (s<s a<=x) (s<s x<b)) → MkRange' x' a<=x x<b $| un R-to-R' |$ \ { x -> s2 x } })}
-}

{-
clause
 (("x'" ,
   arg (arg-info visible (modality relevant quantity-ω))
   (def (quote Nat) []))
  ∷
  ("x<b" ,
   arg (arg-info visible (modality relevant quantity-ω))
   (def (quote _<_)
    (arg (arg-info visible (modality relevant quantity-ω)) (var 0 []) ∷
     arg (arg-info visible (modality relevant quantity-ω)) (var 1 []) ∷
     [])))
  ∷ [])
 (arg (arg-info visible (modality relevant quantity-ω))
  (con (quote MkRange')
   (arg (arg-info visible (modality relevant quantity-ω))
    (con (quote s)
     (arg (arg-info visible (modality relevant quantity-ω)) (var 1) ∷
      []))
    ∷
    arg (arg-info visible (modality relevant quantity-ω))
    (con (quote z<sn) [])
    ∷
    arg (arg-info visible (modality relevant quantity-ω))
    (con (quote s<s)
     (arg (arg-info visible (modality relevant quantity-ω)) (var 0) ∷
      []))
    ∷ []))
  ∷ [])
-}

{-
q != s q of type Nat
when checking the clause left hand side
ANS..extendedlambda (MkRange' (s x') z<sn (s<s x<b))
-}
