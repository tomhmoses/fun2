<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Bool where

open import general-notation
```
-->
# The booleans

```agda
data Bool : Type where
 true false : Bool
```
**Exercise.** Write down the dependent and non-dependent elimination principle for the booleans. Conclude that the non-dependent eliminator amounts to if-then-else.

## Isomorphism with a Basic MLTT type

Strictly speaking, we don't need to add a type of booleans, as above, because it is isomorphic to the type `𝟏 ∔ 𝟏`.

**Exercise.** Define such an isomorphism. There are two isomorphisms, in fact. Define both.

## Some useful functions

```agda
not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true  && y = y
false && y = false

_||_ : Bool → Bool → Bool
true  || y = true
false || y = y

infixr 20 _||_
infixr 30 _&&_

if_then_else_ : {A : Type} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y
```
