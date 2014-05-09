{-# OPTIONS --without-K --type-in-type #-}
module HoTTch2U where

open import HoTTch1U

_^-1 : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
p ^-1 = ind≡ (λ x y p₁ → y ≡ x) refl _ _ p --left those arguments underscored because they're forced and it allows me to leave them implicit

^-1-lemma : {A : Set} {x : A} -> (refl x) ^-1 ≡ (refl x)
^-1-lemma = refl (refl _)

infixr 10 _·_
_·_ : {A : Set} {x y z : A} -> (x ≡ y) -> y ≡ z -> x ≡ z
_·_ {A} {x} {y} {z} p = ind≡ (λ x₁ y₁ p₁ → y₁ ≡ z → x₁ ≡ z) (λ a z₁ → z₁) x y p

-- lemma 2.1.4

lemma-2-1-4-1 : {A : Set} {x y : A} {p : x ≡ y} -> (p ≡ (p · refl y)) × (p ≡ (refl x · p))
lemma-2-1-4-1 {A} {.y} {y} {refl .y} = refl (refl y) , refl (refl y)

lemma-2-1-4-3 : {A : Set} {x y : A} {p : x ≡ y} -> (p ^-1) ^-1 ≡ p
lemma-2-1-4-3 {A} {.y} {y} {refl .y} = refl (refl y)

Ω : (A : Set) -> A -> Set
Ω A a = a ≡ a

Ω² : (A : Set) -> A -> Set
Ω² A a = (refl a) ≡ (refl a)

--- Now for the Eckmann-Hilton argument 
--- first define a general version of the ⋆ operation and whiskering
_∙ᵣ_ : {A : Set} {a b c : A} {p q : a ≡ b} 
       -> (α : p ≡ q) -> (r : b ≡ c) -> (p · r) ≡ (q · r)
_∙ᵣ_ {A} {a} {b} {c} {.q} {q} (refl .q) r = refl _

_∙ₗ_ : {A : Set} {a b c : A} {r s : b ≡ c} -> (p : a ≡ b) -> (β : r ≡ s) -> (p · r) ≡ (p · s)
_∙ₗ_ {A} {a} {b} {c} {.s} {s} p (refl .s) = refl _

-- oh, wait, was too eager this is actually not how they wanted to define whiskering
-- well let's see what happens?
