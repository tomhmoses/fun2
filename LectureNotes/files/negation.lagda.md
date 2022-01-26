<!--
```agda
{-# OPTIONS --without-K --safe #-}

module negation where

open import general-notation
open import prelude
```
-->
## Reasoning with negation

[[This file requires a lot of further work]]

Negation is defined as follows:

```agda
is-empty : Type → Type
is-empty X = X → 𝟘

𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = id

¬_ : Type → Type
¬ X = is-empty X

𝟙-is-nonempty : ¬ is-empty 𝟙
𝟙-is-nonempty f = f ⋆
```

We have the following two proofs of "not false":

```agda
not-false : ¬ 𝟘
not-false = 𝟘-elim

not-false' : ¬ 𝟘
not-false' = id

```

A lot of things about negation don't depend on the fact that the target type of the function type is `𝟘`. We will begin by proving some things about negation by generalizing `𝟘` to any type `R` of "results".

```agda
arrow-contravariance : {A B R : Type}
                     → (A → B)
                     → (B → R) → (A → R)
arrow-contravariance f g = g ∘ f

contrapositive : {A B : Type} → (A → B) → (¬ B → ¬ A)
contrapositive {A} {B} = arrow-contravariance {A} {B} {𝟘}
```

```agda
¬¬ ¬¬¬ : Type → Type
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)
```
```agda
dni : (A R : Type) → A → ((A → R) → R)
dni A R a u = u a

double-negation-intro : (A : Type) → A → ¬¬ A
double-negation-intro A = dni A 𝟘

three-negations-imply-one : (A : Type) → ¬¬¬ A → ¬ A
three-negations-imply-one A = contrapositive (double-negation-intro A)

one-negation-implies-three : (A : Type) → ¬ A → ¬¬¬ A
one-negation-implies-three A = double-negation-intro (¬ A)


```

[[Write code proving that `¬ (Σ x : ℕ , x ≡ x + 1)`.]]
