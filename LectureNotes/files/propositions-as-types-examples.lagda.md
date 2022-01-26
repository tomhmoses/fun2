<!--
```agda
{-# OPTIONS --without-K --safe #-}

module propositions-as-types-examples where

open import general-notation
```
-->
## Examples of propositions as types

```agda
open import
is-even is-odd : ℕ → Type
is-even x = Σ y ꞉ ℕ , (y ≡     2 * x)
is-odd  x = Σ y ꞉ ℕ , (y ≡ 1 + 2 * x)
```
So notice that, under propositions-as-types, we *do not* use *booleans* to interpret logical propositions - we instead use types, as discussed above. The booleans are still useful in some situations, as we will see, but the proposition-as-types interpretation of logic turns out to be generally more useful.

The following illustrates that mutually-recursive definitions in Agda are allowed and that boolean-valued definitions of evenness are possible:
```agda
is-even' is-odd' : ℕ → Bool

is-even' 0       = true
is-even' (suc x) = is-odd' x

is-odd'  0       = false
is-odd'  (suc x) = is-even' x
```

```agda
even-fact : (n : ℕ) → is-even n → is-even' n ≡ true
odd-fact  : (n : ℕ) → is-odd n  → is-odd'  n ≡ true

even-fact 0       e = refl true
even-fact (suc n) e = {!!}
 where
  IH : is-even' n ≡ true
  IH = {!!}


  I : {!!}
  I = {!!}

odd-fact n o = {!!}
```


A boolean-valued equality like in Haskell:
```agda

```


[[Show that inl and inr are distinct]]
