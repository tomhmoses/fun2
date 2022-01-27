<!--
```agda
{-# OPTIONS --without-K --safe #-}

module empty-type where

open import general-notation
```
-->
## The empty type 𝟘

```agda
data 𝟘 : Type where
```

```agda
𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()
```

This may seem a bit disconcerting at first.

```agda
𝟘-nondep-elim : {B : Type} → 𝟘 → B
𝟘-nondep-elim {B} = 𝟘-elim {λ _ → B}
```
