```agda
{-# OPTIONS --without-K --safe #-}

module curry-howard-exercises where

open import curry-howard

data Either (A B : Type) : Type where
 left  : A → Either A B
 right : B → Either A B

∔-iso-Either : (A B : Type) → A ∔ B ≅ Either A B
∔-iso-Either = ?

¬¬ (A + ¬ A) and a more general version

parity

```
Type of the S combinator S f g x = f x (g x)

Show that ∔-elim is a bijection with inverse ∔-split

Show that Σ-elim is a bijection with inverse uncurry.
