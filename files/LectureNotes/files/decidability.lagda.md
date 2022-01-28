<!--
```agda
{-# OPTIONS --without-K --safe #-}

module decidability where

open import prelude
open import negation
```
-->
# Propositions as types versus propositions as booleans

[[Under construction. In particular, we haven't proof-read for typos yet.]]

When programming in Haskell, and indeed in C or Java or Python, etc., we use *booleans* rather than *types* to encode logical propositions.

We now discuss why we use types to encode logical propositions, and
*when* booleans can be used instead. It is not always.  It is here
that the prerequisite *Theories of Computation* shows up.

## Discussion and motivation

In Haskell, we have a function `(==) : Eq a => a -> a -> Bool`. The type constraint `Eq a` is a prerequisite for this function because not all types have decidable equality. What does this mean? It means that, in general, there is no algorithm to decide whether the elements of a type are equal or not.

**Examples.** We *can check* equality of booleans, integers, strings and much more.

**Counter-example.** We *can't check* equality of functions of type `ℕ → ℕ`, for instance. Intuitively, to check that two functions `f` and `g` of this type are equal, we need to check infinitely many cases, namely `f x = g x` for all `x : ℕ`. But, we are afraid, intuition is not enough. This has to be proved. Luckily in our case, [Alan Turing](https://en.wikipedia.org/wiki/Alan_Turing) provided the basis to prove that. He showed that the [Halting Problem](https://en.wikipedia.org/wiki/Halting_problem) can't be solved by an algorithm in any programming language. It follows from this that we can't check whether two such functions `f` and `g` are equal or not using an algorithm.

The above examples and counter-examples show that sometimes we can decide equality with an algorithm, and sometimes we can't. However, for example, the identity type `_≡_` applies to all types, whether they have decidable equality or not, and this is why it is useful. We can think about equality, not only in our heads but also in Agda, without worring whether it can be *checked* to be true or not by a computer. The identity type is not about *checking* equality. In fact, equality is very often not checkable by the computer. It is instead about *stating* and *proving* or *disproving* equalities, where the proving and disproving is done by people (the lecturers and the students in this case), by hard, intellingent work.

## Decidable propositions

Motivated by the above discussion, we define when a logical proposition is decidable under the proposition-as-types understanding of propositions.

```agda
is-decidable : Type → Type
is-decidable A = A ∔ ¬ A
```

This means that there is an algorithm that gives an element of `A` or shows that no such element can be found.

## Decidable propositions as booleans

The following shows that a type `A` is decidable if and only if there is `b : Bool` such that `A` is decidable if and only if the boolean `b` is `true`.

For the purposes of this handout, understanding the following proof is not important. What is important is to understand *what* the type of the following function is saying, which is what we explained above.

We will, however, explain the proof in lectures. We recommend skipping the definition of the following type at a first reading of this handout, and instead concentrate on understading its type only.
```agda
decidability-with-booleans : (A : Type) → is-decidable A ⇔ Σ b ꞉ Bool , (A ⇔ b ≡ true)
decidability-with-booleans A = f , g
 where
  f : is-decidable A → Σ b ꞉ Bool , (A ⇔ b ≡ true)
  f (inl x) = true , (α , β)
   where
    α : A → true ≡ true
    α _ = refl true

    β : true ≡ true → A
    β _ = x

  f (inr ν) = false , (α , β)
   where
    α : A → false ≡ true
    α x = 𝟘-elim (ν x)

    β : false ≡ true → A
    β ()

  g : (Σ b ꞉ Bool , (A ⇔ b ≡ true)) → is-decidable A
  g (true ,  α , β) = inl (β (refl true))
  g (false , α , β) = inr (λ x → false-is-not-true (α x))
```

## Decidable predicates as boolean-valued functions

Consider the logical statement "x is even". This is decidable, because
there is an easy algorithm that tells whether a natural number `x` is
even or not. In programming languages we write this algorithm as a
procedure that returns a boolean. But an equally valid definition is to say that `x` is even if there is a natural number `y` such that `x = 2 * y`. This definition doesn't automatically give an algorithm to check whether or not `x` is odd.
<!--
```agda
module _ where
 private
```
-->
```agda
  is-even : ℕ → Type
  is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
```
This says what to be even *means*. But it doesn't say how we *check* with a computer program whether a number is even or not, which would be given by a function `check-even : ℕ → Bool`. For this function to be correct, it has to be the case that

 > `is-even x ⇔ check-even x ≡ true`

This is possible because

 > `(x : X) → is-decidable (is-even x)`.

The following generalizes the above discussion and implements it in Agda.

First we define what it means for a predicate, such as `is-even`, to be decidable:
```agda
is-decidable-predicate : {X : Type} → (X → Type) → Type
is-decidable-predicate {X} A = (x : X) → is-decidable (A x)

```
In our example, this means that we can tell whether a number is even or not.

Next we show that a predicate `A` is decidable if and only if there is a boolean valued function `α` such that `A x` holds if and only if `α x ≡ true`. In the above example, `A` plays the role of `is-even` and `alpha` plays the role of `check-even`.

Again, what is important at a first reading of this handout is not to understand the proof but what the type of the function is saying. But we will discuss the proof in lectures.

```agda
predicate-decidability-with-booleans : {X : Type} (A : X → Type)
                                     → is-decidable-predicate A
                                     ⇔ Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)
predicate-decidability-with-booleans {X} A = f , g
 where
  f : is-decidable-predicate A → Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)
  f d = α , β
   where
    α : X → Bool
    α x = fst (lr-implication I (d x))
     where
      I : is-decidable (A x) ⇔ Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      I = decidability-with-booleans (A x)

    β : (x : X) → A x ⇔ α x ≡ true
    β x = ϕ , γ
     where
      I : is-decidable (A x) → Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      I = lr-implication (decidability-with-booleans (A x))

      II : Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      II = I (d x)

      ϕ : A x → α x ≡ true
      ϕ = lr-implication (snd II)

      γ : α x ≡ true → A x
      γ = rl-implication (snd II)

  g : (Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)) → is-decidable-predicate A
  g (α , ϕ) = d
   where
    d : is-decidable-predicate A
    d x = III
     where
      I : (Σ b ꞉ Bool , (A x ⇔ b ≡ true)) → is-decidable (A x)
      I = rl-implication (decidability-with-booleans (A x))
      II : Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      II = (α x , ϕ x)
      III : is-decidable (A x)
      III = I II

```

## Decidable equality

A particular case of interest regarding the above discussion is the notion of a type having decidable equality, which can be written in Agda as follows.

```agda
has-decidable-equality : Type → Type
has-decidable-equality X = (x y : X) → is-decidable (x ≡ y)
```
**Exercise.** Show, in Agda, that a type `X` has decidable equality if and only if there is a function `X → X → Bool` that checks whether two elements of `X` are equal or not.`<
