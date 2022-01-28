<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Vector-functions where

open import general-notation
```
-->
# Some functions on vectors

As mentioned in the [introduction](introduction.lagda.md), vectors allow us to have safe `head` and `tail` functions.
```agda
open import Vector
open import natural-numbers-type

head : {A : Type} {n : ℕ} → Vector A (suc n) → A
head (x :: xs) = x

tail : {A : Type} {n : ℕ} → Vector A (suc n) → Vector A n
tail (x :: xs) = xs
```

We can also define a safe indexing function on vectors using [finite types](Fin.lagda.md) as follows.
```agda
open import Fin

_!!_ : ∀ {X n} → Vector X n → Fin n → X
(x :: xs) !! zero  = x
(x :: xs) !! suc n = xs !! n
```

We can also do vector concatenation:
```agda
_++_ : {X : Type} {m n : ℕ} → Vector X m → Vector X n → Vector X (m + n)
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
```
