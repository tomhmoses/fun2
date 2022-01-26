<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-type where

open import general-notation
```
-->
## The binary type 𝟚

This type can be defined to be `𝟙 ∔ 𝟙` using [binary sums](binary-sums.lagda.md), but we give a direct definition which will allow us to discuss some relationships between the various type formers of Basic MLTT.

```agda
data 𝟚 : Type where
 𝟎 𝟏 : 𝟚
```
This type is not only [isomorphic to `𝟙 ∔ 𝟏`](isomorphisms.lagda.md) but also to the type `Bool` os booleans.
Its elimination principle is as follows:
```agda
𝟚-elim : {A : 𝟚 → Type}
       → A 𝟎
       → A 𝟏
       → (x : 𝟚) → A x
𝟚-elim x₀ x₁ 𝟎 = x₀
𝟚-elim x₀ x₁ 𝟏 = x₁
```
In logical terms, this says that it order to prove that a property `A` of elements of the binary type `𝟚` holds for all elements of the type `𝟚`, it is enough to prove that it holds for `𝟎` and for `𝟏`. The non-dependent version of the eliminator is the following:
```agda
𝟚-nondep-elim : {A : Type}
              → A
              → A
              → 𝟚 → A
𝟚-nondep-elim {A} = 𝟚-elim {λ _ → A}
```
