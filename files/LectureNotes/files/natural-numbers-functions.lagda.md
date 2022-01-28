<!--
```agda
{-# OPTIONS --without-K --safe #-}

module natural-numbers-functions where


open import prelude
open import negation
```
-->
# Natural numbers functions, relations and properties

## Some general properties

```agda
suc-is-not-zero : {x : ℕ} → suc x ≢ 0
suc-is-not-zero ()

pred : ℕ → ℕ
pred 0       = 0
pred (suc n) = n

suc-left-cancellable : {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-left-cancellable = ap pred

+-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc x y z = {!!}

+-0-on-right : (x : ℕ) → x + 0 ≡ x
+-0-on-right x = {!!}

+-suc-on-right : (x y : ℕ) → x + suc y ≡ suc (x + y)
+-suc-on-right x y = {!!}

+-commutative : (x y : ℕ) → x + y ≡ y + x
+-commutative x y = {!!}

+-right-cancellable : (x y z : ℕ) → x + z ≡ y + z → x ≡ y
+-right-cancellable x y z p = {!!}
```

## Order relation _≤_

The less-than order on natural numbers can be defined in a number of
equivalent ways. The first one says that `x ≤ y` iff `x + z ≡ y` for
some `z`:
```agda
_≤₀_ : ℕ → ℕ → Type
x ≤₀ y = Σ a ꞉ ℕ , x + a ≡ y
```
The second one is defined by recursion:
```agda
_≤₁_ : ℕ → ℕ → Type
0     ≤₁ y     = 𝟙
suc x ≤₁ 0     = 𝟘
suc x ≤₁ suc y = x ≤₁ y
```
The third one, which we will as the official one, is defined *by induction* using `data`:
```agda
data _≤_ : ℕ → ℕ → Type where
 0-smallest      : {y : ℕ} → 0 ≤ y
 suc-preserves-≤ : {x y : ℕ} → x ≤ y → suc x ≤ suc y

_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x
```

We will now show some properties of these relations.
```agda
suc-reflects-≤ : {x y : ℕ} → suc x ≤ suc y → x ≤ y
suc-reflects-≤ {x} {y} (suc-preserves-≤ l) = l

suc-preserves-≤₀ : {x y : ℕ} → x ≤₀ y → suc x ≤₀ suc y
suc-preserves-≤₀ {x} {y} (a , p) = γ
 where
  q : suc (x + a) ≡ suc y
  q = ap suc p

  γ : suc x ≤₀ suc y
  γ = (a , q)

≤₀-implies-≤₁ : {x y : ℕ} → x ≤₀ y → x ≤₁ y
≤₀-implies-≤₁ {zero}  {y}     (a , p) = ⋆
≤₀-implies-≤₁ {suc x} {suc y} (a , p) = IH
 where
  q : x + a ≡ y
  q = suc-left-cancellable p

  γ : x ≤₀ y
  γ = (a , q)

  IH : x ≤₁ y
  IH = ≤₀-implies-≤₁ {x} {y} γ

≤₁-implies-≤ : {x y : ℕ} → x ≤₁ y → x ≤ y
≤₁-implies-≤ {zero}  {y}     l = 0-smallest
≤₁-implies-≤ {suc x} {suc y} l = γ
 where
  IH : x ≤ y
  IH = ≤₁-implies-≤ l

  γ : suc x ≤ suc y
  γ = suc-preserves-≤ IH

≤-implies-≤₀ : {x y : ℕ} → x ≤ y → x ≤₀ y
≤-implies-≤₀ {0}     {y}      0-smallest         = (y , refl y)
≤-implies-≤₀ {suc x} {suc y} (suc-preserves-≤ l) = γ
 where
  IH : x ≤₀ y
  IH = ≤-implies-≤₀ {x} {y} l

  γ : suc x ≤₀ suc y
  γ = suc-preserves-≤₀ IH
```

## Prime numbers

```agda
is-prime : ℕ → Type
is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) ∔ (x ≡ n))

twin-prime-conjecture : Type
twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n)
                                          × is-prime p
                                          × is-prime (p + 2)
```

**Exercise.** Show that `is-prime n` is [decidable](decidability.lagda.md) for every `n : ℕ`.
