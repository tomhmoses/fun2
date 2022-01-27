<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Fin where

open import general-notation
```
-->
# Finite types

We now define a type `Fin n` which has exactly `n` elements, where `n : ℕ` is a natural number.

```agda
open import natural-numbers-type public

data Fin : ℕ → Type where
 zero : {n : ℕ} → Fin (suc n)
 suc  : {n : ℕ} → Fin n → Fin (suc n)
```
Examples:
```agda
private
 x₀ x₁ x₂ : Fin 3
 x₀ = zero
 x₁ = suc zero
 x₂ = suc (suc zero)
```
And these are all the elements of `Fin 3`. Notice that `Fin 0` is empty:
```agda

open import negation public

Fin-0-is-empty : is-empty (Fin 0)
Fin-0-is-empty ()
```
Here `()` is a pseudo-pattern that tells that there is no constructor for the type.
```agda
Fin-suc-is-nonempty : {n : ℕ} → ¬ is-empty (Fin (suc n))
Fin-suc-is-nonempty f = f zero
```

TODO. The above proofs require more explanation.

## Elimination principle

```agda
Fin-elim : (A : {n : ℕ} → Fin n → Type)
         → ({n : ℕ} → A {suc n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (suc k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim A a f = h
 where
  h : {n : ℕ} (k : Fin n) → A k
  h zero    = a
  h (suc k) = f k (h k)
```
So this again looks like [primitive recursion](natural-numbers-types.lagda.md). And it gives an induction principle for `Fin`.

## Isomorphism with a Basic MLTT type

```agda
open import empty-type
open import unit-type
open import binary-sums
open import isomorphisms
open import identity-type
open import products

Fin' : ℕ → Type
Fin' zero    = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc n) zero    = zero'
  f (suc n) (suc k) = suc' (f n k)

  g : (n : ℕ) → Fin' n → Fin n
  g (suc n) (inl ⋆) = zero
  g (suc n) (inr k) = suc (g n k)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero    = refl zero
  gf (suc n) (suc k) = γ
   where
    IH : g n (f n k) ≡ k
    IH = gf n k

    γ = g (suc n) (f (suc n) (suc k)) ≡⟨ refl _ ⟩
        g (suc n) (suc' (f n k))      ≡⟨ refl _ ⟩
        suc (g n (f n k))             ≡⟨ ap suc IH ⟩
        suc k                         ∎

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (inl ⋆) = refl (inl ⋆)
  fg (suc n) (inr k) = γ
   where
    IH : f n (g n k) ≡ k
    IH = fg n k

    γ = f (suc n) (g (suc n) (suc' k)) ≡⟨ refl _ ⟩
        f (suc n) (suc (g n k))        ≡⟨ refl _ ⟩
        suc' (f n (g n k))             ≡⟨ ap suc' IH ⟩
        suc' k                         ∎

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n}
```
**Exercise.** Show that the type `Fin n` is isormorphic to the type `Σ k : ℕ , k < n`.

TODO. Explain much more in this handout.
