<!--
```agda
{-# OPTIONS --without-K --safe #-}

module decidability where

open import prelude
open import negation
```
-->
# Decidability

A lot more to add here. This is just the beginning.

## Decidable types

```agda
is-decidable : Type → Type
is-decidable X = X ∔ ¬ X

is-decidable-predicate : {X : Type} → (X → Type) → Type
is-decidable-predicate {X} A = (x : X) → is-decidable (A x)
```

TODO. Put this in some other file:
```agda
false-is-not-true : false ≢ true
false-is-not-true ()
```


```agda
decidability-with-booleans : {X : Type} → is-decidable X ⇔ Σ b ꞉ Bool , (X ⇔ b ≡ true)
decidability-with-booleans {X} = f , g
 where
  f : is-decidable X → Σ b ꞉ Bool , (X ⇔ b ≡ true)
  f (inl x) = true , (α , β)
   where
    α : X → true ≡ true
    α _ = refl true

    β : true ≡ true → X
    β _ = x

  f (inr ν) = false , (α , β)
   where
    α : X → false ≡ true
    α x = 𝟘-elim (ν x)

    β : false ≡ true → X
    β ()

  g : (Σ b ꞉ Bool , (X ⇔ b ≡ true)) → is-decidable X
  g (true ,  α , β) = inl (β (refl true))
  g (false , α , β) = inr (λ x → false-is-not-true (α x))
```

```agda
predicate-decidability-with-booleans : {X : Type} (A : X → Type)
                                     → is-decidable-predicate A
                                     ⇔ Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)
predicate-decidability-with-booleans {X} A = f , g
 where
  f : is-decidable-predicate A → Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)
  f = {!!}

  g : (Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)) → is-decidable-predicate A
  g = {!!}

```


## Decidable equality

```agda
has-decidable-equality : Type → Type
has-decidable-equality X = (x y : X) → is-decidable (x ≡ y)
```
