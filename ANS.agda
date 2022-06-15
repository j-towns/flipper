open import Reverse using (_<->_; MkRev; _$|_|$_; un)
open import Util

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (Nat) renaming (zero to z; suc to s; _+_ to _+N_; _*_ to _*N_)

open _<->_


_**N_ : Nat -> Nat -> Nat
a **N z = s z
a **N s n = a *N (a **N n)

infix 8 _**N_

≡-symm : {A : Set}{a b : A} -> a ≡ b -> b ≡ a
≡-symm {_} {a} {.a} refl = refl

+N-comm : (a b : Nat) -> (a +N b) ≡ (b +N a)
+N-comm z z = refl
+N-comm (s a) z rewrite +N-comm a z = refl
+N-comm z (s b) rewrite ≡-symm (+N-comm z b) = refl
+N-comm (s a) (s b) rewrite +N-comm a (s b) | ≡-symm (+N-comm (s a) b) | +N-comm a b = refl

+N-idr : (a : Nat) -> a +N z ≡ a
+N-idr z = refl
+N-idr (s a) rewrite +N-idr a = refl

*N-assoc : (a b c : Nat) -> a *N (b *N c) ≡ (a *N b) *N c
*N-assoc a b c = {!!}

data Range : Nat -> Nat -> Set where
  z  : {b : Nat}                -> Range z     (s b)
  s1 : {b : Nat}   -> Range z b -> Range z     (s b)
  s2 : {a b : Nat} -> Range a b -> Range (s a) (s b)

Fin : Nat -> Set
Fin b = Range z b

to-Nat : {a b : Nat} -> Range a b -> Nat
to-Nat z = z
to-Nat (s1 n) = s (to-Nat n)
to-Nat (s2 n) = s (to-Nat n)

move : {a b : Nat} (c : Nat) -> Range a b <-> Range (c +N a) (c +N b)
move z     = MkRev \ { n ->                           n        }
move (s c) = MkRev \ { n -> n $| move c |$ \ { n+c -> s2 n+c } }

split : {a c : Nat} -> (b : Range a (s c)) -> Range a c <-> Range a (to-Nat b) + Range (to-Nat b) c
split z = MkRev (\ { n -> inr n })
split {_} {s c} (s1 b) = MkRev \ { n ->
                                     n  $| part1 |$ \ { n'  ->
                                     n' $| part2 |$ \ { n'' ->
                                   n'' }}}
  where
  part1 : Range z (s c) <-> One + Range z (to-Nat b) + Range (to-Nat b) c
  part1 = MkRev \ { z      → inl <>
                  ; (s1 n) →
                      n $| split b |$ \ { n' ->
                    inr n' }}

  part2 : One + Range z (to-Nat b) + Range (to-Nat b) c <-> Range z (s (to-Nat b)) + Range (s (to-Nat b)) (s c)
  part2 = MkRev (\ { (inl <>)       → inl z
                   ; (inr (inl n')) → inl (s1 n')
                   ; (inr (inr n')) → inr (s2 n') })
split {s a} {s c} (s2 b) = MkRev (\ { (s2 n) → n $| split b |$ \ { n' -> n' $| helper |$ \ { n'' -> n'' } } })
  where
  helper : Range a (to-Nat b) + Range (to-Nat b) c <->  Range (s a) (s (to-Nat b)) + Range (s (to-Nat b)) (s c)
  helper = MkRev (\ { (inl n) → inl (s2 n)
                    ; (inr n) → inr (s2 n) })

data _<_ : Nat -> Nat -> Set where
  z<sn : {o : Nat}            -> z   < s o
  s<s  : {p q : Nat} -> p < q -> s p < s q

infix 1 _<_

_≤_ : Nat -> Nat -> Set
a ≤ b = a < s b

infix 1 _≤_

data Compare (a b : Nat) : Set where
  LT : a < b -> Compare a b
  EQ : a ≡ b -> Compare a b
  GT : b < a -> Compare a b

compare : (a b : Nat) -> Compare a b
compare z     z     = EQ refl
compare (s a) z     = GT z<sn
compare z     (s b) = LT z<sn
compare (s a) (s b) with compare a b
... | LT p    = LT (s<s p)
... | EQ refl = EQ refl
... | GT p    = GT (s<s p)

postulate
  scale : {a b c : Nat} -> Range (c *N a) (c *N b) <-> Range a b * Fin c

Message : (a b : Nat) -> Set
Message a b = Range a (b *N a) * List (Fin b) + Fin a

<-helper : (a a' : Nat) -> a ≤ a' -> a' < a -> Zero
<-helper (s a) z (s<s ()) a'<a
<-helper (s a) (s a') (s<s a<a'+1) (s<s a'<a) with <-helper a a' a<a'+1 a'<a
... | ()

<-step : {a b : Nat} -> a < b -> a < s b
<-step {z}   a<b       = z<sn
<-step {s a} (s<s a<b) = s<s (<-step a<b)

≡-implies-≤ : {a b : Nat} -> a ≡ b -> a ≤ b
≡-implies-≤ {z} {.z} refl = z<sn
≡-implies-≤ {s a} {.(s a)} refl = s<s (≡-implies-≤ refl)

a≤a : {a : Nat} -> a ≤ a
a≤a {a} = ≡-implies-≤ refl

rebase-lemma-helper : (a a' b : Nat) -> 0 < a -> a < a' -> 2 ≤ b
  -> Σ Nat (\ n -> (b **N n *N a  ≤ a') * (a' ≤ b *N (b **N n *N a )))
rebase-lemma-helper a (s a') b 0<a a<a'+1 2≤b with compare a a'
rebase-lemma-helper a (s a') b 0<a a<a'+1 2≤b | LT a<a' with rebase-lemma-helper a a' b 0<a a<a' 2≤b
rebase-lemma-helper a (s a') b 0<a a<a'+1 2≤b | LT a<a' | n , ab**n≤a' , a'≤ab**[n+1] with compare (s a') (b *N (b **N n *N a ))
rebase-lemma-helper a (s a') b 0<a a<a'+1 2≤b | LT a<a' | n , ab**n≤a' , a'≤ab**[n+1] | LT a'+1<ab**[n+1] = n , <-step ab**n≤a' , <-step a'+1<ab**[n+1]
rebase-lemma-helper a (s a') b 0<a a<a'+1 2≤b | LT a<a' | n , ab**n≤a' , a'≤ab**[n+1] | EQ a'+1≡ab**[n+1] = n , <-step ab**n≤a' , ≡-implies-≤ a'+1≡ab**[n+1]
rebase-lemma-helper a (s a') b 0<a a<a'+1 2≤b | LT a<a' | n , ab**n≤a' , a'≤ab**[n+1] | GT a'+1>ab**[n+1] rewrite *N-assoc b (b **N n) a = s n , <-step a'+1>ab**[n+1] , {!!}
rebase-lemma-helper a (s .a) b 0<a a<a'+1 2≤b | EQ refl = z , (helper a {b} , {!!})
  where
  helper : ∀ a {b} → b **N z *N a < s (s a)
  helper z = z<sn
  helper (s a) = s<s (helper a {b})
rebase-lemma-helper a (s a') b 0<a a<a'+1 2≤b | GT a'<a with <-helper a a' a<a'+1 a'<a
... | ()

rebase-lemma : (a a' b : Nat) -> 0 < a -> 0 < a' -> 2 ≤ b
  -> Σ Nat (\ n -> (b **N n *N a  ≤ a') * (a' ≤ b *N (b **N n *N a ))
                 + (b **N n *N a' ≤ a ) * (a  ≤ b *N (b **N n *N a')))
rebase-lemma a a' b 0<a 0<a' 2≤b with compare a a'
rebase-lemma a a' b 0<a 0<a' 2≤b | LT a<a' with rebase-lemma-helper a a' b 0<a a<a' 2≤b
rebase-lemma a a' b 0<a 0<a' 2≤b | LT a<a' | n , p = n , inl p
rebase-lemma a .a b 0<a 0<a' 2≤b | EQ refl = z , inl {!!} --- Similar lemma to above
rebase-lemma a a' b 0<a 0<a' 2≤b | GT a'<a with rebase-lemma-helper a' a b 0<a' a'<a 2≤b
rebase-lemma a a' b 0<a 0<a' 2≤b | GT a'<a | n , p = n , inr p

rebase-helper1 : (a b n : Nat) -> Message a b <-> Message (b **N n *N a) b
rebase-helper1 a b n = {!!}

rebase-helper2 : (a b c : Nat) -> a ≤ c -> c ≤ b *N a -> Message a b <-> Message c b
rebase-helper2 a b c = {!!}

rebase : {a a' b : Nat} -> {0 < a} -> {0 < a'} -> {2 ≤ b} -> Message a b <-> Message a' b
rebase {a} {a'} {b} {0<a} {0<a'} {2≤b} with rebase-lemma a a' b 0<a 0<a' 2≤b
rebase {a} {a'} {b} {0<a} {0<a'} {2≤b} | n , inl (ab**n≤a' , a'≤ab**[n+1]) = MkRev (\ {
  x ->
    x  $| rebase-helper1 a b n                                     |$ \ { x'  -> 
    x' $| rebase-helper2 (b **N n *N a) b a' ab**n≤a' a'≤ab**[n+1] |$ \ { x'' -> x'' } } }) {{!!}}
rebase {a} {a'} {b} | n , inr (a'b**n≤a , a≤a'b**[n+1]) = {!!}

{-
macro
  dump : ({b : Nat} -> Σ Nat (λ m → (z < m) * (m < s b)) -> Σ Nat (λ m → m < b)) -> Term -> TC ⊤
  dump f hole =
    bindTC (quoteTC f) \ `f ->
    bindTC (quoteTC `f) \ ``f ->
    typeError (termErr ``f ∷ [])
-}

record Range' (a b : Nat) : Set where
  constructor MkRange'
  field
    x    : Nat
    a<=x : a ≤ x
    x<b  : x < b

R-to-R' : {a b : Nat} -> Range a b <-> Range' a b
R-to-R' = MkRev \ { z      ->                                               MkRange' z      z<sn       z<sn
                  ; (s1 x) -> x $| R-to-R' |$ \ { (MkRange' x' z<sn x<b) -> MkRange' (s x') z<sn       (s<s x<b) }
                  ; (s2 x) -> x $| R-to-R' |$ \ { (MkRange' x' a<=x x<b) -> MkRange' (s x') (s<s a<=x) (s<s x<b) } }

move' : {a b : Nat} (c : Nat) -> Range' a b <-> Range' (c +N a) (c +N b)
move' {a} {b} z     = MkRev \ { n -> n }
move' {a} {b} (s c) = MkRev \ { n -> n $| move' c |$ \ { (MkRange' c+n c+a<=c+n c+n<c+b) → MkRange' (s c+n) (s<s c+a<=c+n) (s<s c+n<c+b) }}

