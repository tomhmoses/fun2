<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-trees-type where

open import prelude
```
-->
# Binary trees and their size and height

```agda
data BT (A : Type) : Type where
 leaf : BT A
 node : A → BT A → BT A → BT A
```
We also consider binary trees without labels at the nodes or leaves, which we call *skeletal binary trees*:
```agda
data SBT : Type where
 leaf : SBT
 node : SBT → SBT → SBT
```
** Exercise.** Define the elimination principle for the types `BT and ``SBT`.

```agda
skeleton : {A : Type} → BT A → SBT
skeleton leaf         = leaf
skeleton (node x t u) = node (skeleton t) (skeleton u)
```

## Full binary trees, size and height

We work with skeletal binary trees for simplicity.

```agda

full-tree : ℕ → SBT
full-tree 0       = leaf
full-tree (suc n) = node (full-tree n) (full-tree n)

```
We define the size to be the number of nodes:
```agda
size : SBT → ℕ
size leaf       = 0
size (node t u) = 1 + size t + size u
```
TODO. The following properties may need adjustment to be true:
```agda
open import natural-numbers-functions

height : SBT → ℕ
height leaf       = 0
height (node t u) = 1 + max (height t) (height u)
```
```agda
size-of-full-tree : (n : ℕ) → size (full-tree n) + 1 ≡ 2 ^ n
size-of-full-tree n = {!!}

height-of-full-tree : (n : ℕ) → height (full-tree n) ≡ n
height-of-full-tree n = {!!}

is-full : SBT → Type
is-full t = Σ n ꞉ ℕ , t ≡ full-tree n

size-of-full-trees : (t : SBT)
                   → is-full t
                   → size t + 1 ≡ 2 ^ (height t)
size-of-full-trees t = {!!}

```
In general:
```agda
size-height-relation : (t : SBT) → size t + 1 ≤ 2 ^ (height t)
size-height-relation t = {!!}
```
