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

_⋆_ : {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} -> (α : p ≡ q) -> (β : r ≡ s) -> (p · r) ≡ (q · s)
_⋆_ {A} {a} {b} {c} {p} {q} {r} {s} α β = α ∙ᵣ r · q ∙ₗ β

-- TODO finish this section

ap : {A B : Set} {x y : A} -> (f : A -> B) -> x ≡ y -> (f x) ≡ (f y)
ap f (refl _) = refl _

-- transport

transport : {A : Set} {x y : A} -> (B : A -> Set) -> (p : x ≡ y) -> B x -> B y
transport {A} {.y} {y} B (refl .y) bx = bx

lift : {A : Set} {B : A -> Set} {x y : A} -> (u : B x) -> (p : x ≡ y) -> (x , u) ≡ (y , transport B p u)
lift {A} {B} {.y} {y} u (refl .y) = refl _

lift-prop : {A : Set} {B : A -> Set} {x y : A} -> (u : B x) -> (p : x ≡ y) -> (ap {Σ A B} pr₁ (lift u p)) ≡ p
lift-prop {A} {B} {.y} {y} u (refl .y) = refl (refl y) -- so how does this work? because lift just returns refl, on refl, right?

apd : {A : Set} {B : A -> Set} {x y : A} -> (f : (a : A) -> B a) 
            -> (p : x ≡ y) -> (transport B p (f x)) ≡ (f y)
apd {A} {B} {.y} {y} f (refl .y) = refl (f y)

lemma-2-3-5 : {A B : Set} {x y : A} -> (p : x ≡ y) -> (b : B) -> (transport (λ _ -> B) p b) ≡ b
lemma-2-3-5 {A} {B} {.y} {y} (refl .y) b = refl b

lemma-2-3-8 : {A B : Set} {x y : A} -> (f : A -> B) -> (p : x ≡ y)
            -> (apd f p) ≡ ((lemma-2-3-5 p (f x)) · (ap f p))
lemma-2-3-8 {A} {B} {.y} {y} f (refl .y) = refl (refl (f y)) -- this is scary easy

lemma-2-3-9 : {A : Set} {P : A -> Set} {x y z : A} -> (p : x ≡ y) -> (q : y ≡ z)
             -> (u : P x) 
             -> (transport P q (transport P p u)) ≡ (transport P (p · q) u)
lemma-2-3-9 {A} {P} {.y} {y} (refl .y) q u = refl _

