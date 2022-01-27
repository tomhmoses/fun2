<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Maybe where

open import general-notation
```
-->
# The `Maybe` type constructor

```agda

data Maybe (X : Type) : Type where
  nothing : Maybe X
  just    : X → Maybe X
```

## Elimination principle

```agda
Maybe-elim : {X : Type} {A : Maybe X → Type}
           → A nothing
           → ((x : X) → A (just x))
           → (m : Maybe X) → A m
Maybe-elim a f nothing  = a
Maybe-elim a f (just x) = f x
```

## Isomorphism with a Basic MLTT type

```agda
open import unit-type
open import binary-sums
open import isomorphisms
open import products
open import identity-type

Maybe-isomorphism : (X : Type) → Maybe X ≅ 𝟙 ∔ X
Maybe-isomorphism X = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Maybe X → 𝟙 ∔ X
  f nothing  = inl ⋆
  f (just x) = inr x

  g : 𝟙 ∔ X → Maybe X
  g (inl ⋆) = nothing
  g (inr x) = just x

  gf : g ∘ f ∼ id
  gf nothing = refl nothing
  gf (just x) = refl (just x)

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr x) = refl (inr x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg}
```

TODO. Explain much more in this handout.
