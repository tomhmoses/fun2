<!--
```agda
{-# OPTIONS --without-K --safe #-}

module limbo where

open import general-notation
```
-->
# Limbo

Use this file as a place holder for things that should go somewhere else. This file is not supposed to be imported. It is for temporary work only. This file may not even type check, and this is fine.

## More types

Recall some types we already discussed:

```agda

data Maybe (A : Type) : Type where
 nothing : Maybe A
 just    : A → Maybe A

data Either (A B : Type) : Type where
 left  : A → Either A B
 right : B → Either A B

data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

data Vector (A : Type) : ℕ → Type where
 []   : Vector A 0
 _::_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

infixr 10 _::_
```

It turns out these types are isomorphic to types that can be defined in Basic Martin-Löf Type Theory.
And here is another type which is isomorphic to a type definable in Basic MLTT, as we shall see:
```agda
data Fin : ℕ → Type where
 zero : {n : ℕ} → Fin (suc n)
 succ : {n : ℕ} → Fin n → Fin (suc n)
```
