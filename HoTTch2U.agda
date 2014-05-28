{-# OPTIONS --without-K --type-in-type #-}
module HoTTch2U where

open import HoTTch1U hiding (Σ ; _×_ ; _,_ )
open import Relation.Binary.PropositionalEquality
open import Data.Product
open ≡-Reasoning

_^-1 : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
p ^-1 = ind≡ (λ x y p₁ → y ≡ x) (λ a → refl {x = a}) _ _ p --left those arguments underscored because they're forced and it allows me to leave them implicit

^-1-lemma : {A : Set} {x : A} -> refl {x = x} ^-1 ≡ refl {x = x}
^-1-lemma = refl {x = refl}

module CompInd where
  _·_ : {A : Set} {x y z : A} -> (x ≡ y) -> y ≡ z -> x ≡ z
  _·_ {A} {x} {y} {z} p = ind≡ (λ x₁ y₁ p₁ → y₁ ≡ z → x₁ ≡ z) (λ a z₁ → z₁) x y p


infixr 10 _·_
_·_ : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
_·_ refl q = q



lassoc : {A : Set} {w x y z : A} -> (p : x ≡ y) -> (q : y ≡ z) -> (r : z ≡ w) ->
       p · ( q · r) ≡ (p · q) · r
lassoc refl q r = refl

rassoc : {A : Set} {w x y z : A} -> (p : x ≡ y) -> (q : y ≡ z) -> (r : z ≡ w) ->
       (p · q) · r ≡ p · ( q · r)
rassoc p q r = sym (lassoc p q r)

lid : {A : Set} {x y : A} {p : x ≡ y} -> (p · refl) ≡ p
lid {A} {.y} {y} {refl} = refl

rid : {A : Set} {x y : A} {p : x ≡ y} -> (refl · p) ≡ p
rid {A} {.y} {y} {refl} = refl

invinv : {A : Set} {x y : A} -> (p : x ≡ y) -> (p ^-1) ^-1 ≡ p
invinv refl = refl

linv : {A : Set} {x y : A} -> (p : x ≡ y) -> (p ^-1) · p ≡ refl
linv refl = refl

rinv : {A : Set} {x y : A} -> (p : x ≡ y) -> p · (p ^-1) ≡ refl
rinv refl = refl

-- lemma 2.1.4

lemma-2-1-4-1 : {A : Set} {x y : A} {p : x ≡ y} -> (p ≡ (p · refl)) × (p ≡ (refl · p))
lemma-2-1-4-1 {A} {.y} {y} {refl} = refl { x = refl} , refl

lemma-2-1-4-3 : {A : Set} {x y : A} {p : x ≡ y} -> (p ^-1) ^-1 ≡ p
lemma-2-1-4-3 {A} {.y} {y} {refl} = refl {x = refl {x = y} }
-- maybe it's silly I'm putting in all the implicity arguments but I'm trying to not be obtuse about what all the types are doing 

Ω : (A : Set) -> A -> Set
Ω A a = a ≡ a

Ω² : (A : Set) -> A -> Set
Ω² A a = (refl {x = a}) ≡ refl


--- Now for the Eckmann-Hilton argument 
--- first define a general version of the ⋆ operation and whiskering
_∙ᵣ_ : {A : Set} {a b c : A} {p q : a ≡ b} 
       -> (α : p ≡ q) -> (r : b ≡ c) -> (p · r) ≡ (q · r)
_∙ᵣ_ refl r = refl

_∙ₗ_ : {A : Set} {a b c : A} {r s : b ≡ c} -> (p : a ≡ b) -> (β : r ≡ s) -> (p · r) ≡ (p · s)
_∙ₗ_ p refl = refl


-- oh, wait, was too eager this is actually not how they wanted to define whiskering
-- well let's see what happens?

_⋆_ : {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} -> (α : p ≡ q) -> (β : r ≡ s) -> (p · r) ≡ (q · s)
_⋆_ {A} {a} {b} {c} {p} {q} {r} {s} α β = α ∙ᵣ r · q ∙ₗ β

-- TODO finish this section

ap : {A B : Set} {x y : A} -> (f : A -> B) -> x ≡ y -> (f x) ≡ (f y)
ap f refl = refl

id : {A : Set} -> A -> A
id x = x

ap-id : {A : Set} {x y : A} -> (p : x ≡ y) -> ap id p ≡ p
ap-id refl = refl

-- transport

transport : {A : Set} {x y : A} -> (B : A -> Set) -> (p : x ≡ y) -> B x -> B y
transport {A} {.y} {y} B refl bx = bx

lift : {A : Set} {B : A -> Set} {x y : A} -> (u : B x) -> (p : x ≡ y) -> (x , u) ≡ (y , transport B p u)
lift {A} {B} {.y} {y} u refl = refl

lift-prop : {A : Set} {B : A -> Set} {x y : A} -> (u : B x) -> (p : x ≡ y) -> (ap {Σ A B} proj₁ (lift u p)) ≡ p
lift-prop {A} {B} {.y} {y} u refl = refl -- so how does this work? because lift just returns refl, on refl, right?

apd : {A : Set} {B : A -> Set} {x y : A} -> (f : (a : A) -> B a) 
            -> (p : x ≡ y) -> (transport B p (f x)) ≡ (f y)
apd {A} {B} {.y} {y} f refl = refl

lemma-2-3-5 : {A B : Set} {x y : A} -> (p : x ≡ y) -> (b : B) -> (transport (λ _ -> B) p b) ≡ b
lemma-2-3-5 {A} {B} {.y} {y} refl b = refl

lemma-2-3-8 : {A B : Set} {x y : A} -> (f : A -> B) -> (p : x ≡ y)
            -> (apd f p) ≡ ((lemma-2-3-5 p (f x)) · (ap f p))
lemma-2-3-8 {A} {B} {.y} {y} f refl = refl -- this is scary easy

lemma-2-3-9 : {A : Set} {P : A -> Set} {x y z : A} -> (p : x ≡ y) -> (q : y ≡ z)
             -> (u : P x) 
             -> (transport P q (transport P p u)) ≡ (transport P (p · q) u)
lemma-2-3-9 {A} {P} {.y} {y} refl q u = refl

_~_ : {A : Set} {P : A -> Set} -> (f g : (x : A) -> P x) -> Set
f ~ g = (x : _) → f x ≡ g x

-- lemma 2.4.3 natural transformation (ish?)

natH : {A B : Set} {f g : A -> B} {x y : A} -> (H : f ~ g) 
     -> (p : x ≡ y) -> ((H x) · (ap g p)) ≡ ((ap f p) · (H y))
natH {A} {B} {f} {g} {.y} {y} H refl = aux (H y)
  where aux : {S : Set} {a b : S} -> (p : a ≡ b) -> (p · refl) ≡ p 
        aux {S} {.b} {b} refl = refl

-- corollary 2.4.4, grr the type is deceptive at first
exchange : {A : Set} (f : A -> A) -> (H : f ~ id) -> (x : A) -> (H (f x)) ≡ (ap f (H x))
exchange f H x = sym aux₃ where
  aux₁ : H (f x) · ap (λ z → z) (H x) ≡ ap (λ z → f z) (H x) · H x
  aux₁ = natH H (H x)
  
  aux₂ : (ap f (H x)) · (H x) ≡ ((H (f x) · H x))
  aux₂ = sym (transport (λ p → H (f x) · p ≡ ap (λ z → f z) (H x) · H x) (ap-id (H x)) aux₁)
  -- uhh why did we do the symmetry? Oh, right, the book kinda did so wevs

  aux₃ : ap f (H x) ≡ H (f x)
  aux₃ = begin ap f (H x) 
            ≡⟨ sym lid ⟩
               ap f (H x) · refl
            ≡⟨ cong (λ p → ap f (H x) · p) (sym (rinv (H x))) ⟩ 
               ap f (H x) · H x · H x ^-1 
            ≡⟨ lassoc (ap f (H x)) (H x) (ind≡ (λ x₁ y _ → y ≡ x₁) (λ a → refl) (f x) x (H x)) ⟩ 
               (ap f (H x) · H x) · H x ^-1 
            ≡⟨ cong (λ p → p · H x ^-1) aux₂ ⟩ 
               (H (f x) · H x) · H x ^-1 
            ≡⟨ rassoc (H (f x)) (H x) (ind≡ (λ x₁ y _ → y ≡ x₁) (λ a → refl) (f x) x (H x)) ⟩ 
               H (f x) · H x · H x ^-1 
            ≡⟨ cong (λ p → H (f x) · p) (rinv (H x)) ⟩ 
               H (f x) · refl 
            ≡⟨ lid ⟩ 
               (H (f x) ∎)
-- alright, we're finally done with this proof!

quasi-inverse : {A B : Set} -> (f : A -> B) -> Set
quasi-inverse {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id × (g ∘ f) ~ id)

qiId : {A : Set} -> quasi-inverse {A} {A} id
qiId = id , (λ x → refl) , (λ x → refl)

qiPath : {A : Set} {x y z : A} -> (p : x ≡ y) -> quasi-inverse ((λ (q : y ≡ z) -> p · q))
qiPath refl = id , (λ x → refl) , (λ x → refl) -- this was so easy, it scares the crap out of me, so let's try the harder way

qiPath' : {A : Set} {x y z : A} -> (p : x ≡ y) -> quasi-inverse ((λ (q : y ≡ z) -> p · q))
qiPath' {A} {x} {y} {z} p = (λ q → p ^-1 · q) , (aux₁ , aux₂) where
   aux₁ : (r : x ≡ z) -> (p · (p ^-1 · r)) ≡ r
   aux₁ r = begin p · p ^-1 · r 
               ≡⟨ lassoc p (ind≡ (λ x₁ y₁ _ → y₁ ≡ x₁) (λ a → refl) x y p) r ⟩ 
                  (p · p ^-1) · r 
               ≡⟨ cong (λ s → s · r) (rinv p) ⟩ 
                  refl · r 
               ≡⟨ rid ⟩ 
                  (r ∎)
  
   aux₂ : (r : y ≡ z) -> (p ^-1 · (p · r)) ≡ r
   aux₂ r = begin p ^-1 · p · r 
               ≡⟨ lassoc (ind≡ (λ x₁ y₁ _ → y₁ ≡ x₁) (λ a → refl) x y p) p r ⟩ 
                  (p ^-1 · p) · r 
               ≡⟨ cong (λ s → s · r) (linv p) ⟩ 
                  refl · r 
               ≡⟨ rid ⟩ 
                 (r ∎)

qiTransport : {A : Set} {B : A -> Set} {x y : A} -> (p : x ≡ y) -> quasi-inverse (transport B p)
qiTransport {A} {B} {x} {y} p = transport B (p ^-1) , aux₁ , aux₂ where 
-- we coooouuuulllllldddd just do path induction again but that seems like chorting
   aux₁ : (b : B y) -> transport B p (transport B (p ^-1) b) ≡ b
   aux₁ b = begin transport B p (transport B (p ^-1) b) 
               ≡⟨ lemma-2-3-9 {A} {B} {y} {x} {_} (p ^-1) p b ⟩ 
                  transport B (p ^-1 · p) b 
               ≡⟨ cong (λ s → transport B s b) (linv p) ⟩ 
                  transport B refl b 
               ≡⟨ refl ⟩ 
                  (b ∎)

   aux₂ : (b : B x) -> transport B (p ^-1) (transport B p b) ≡ b
   aux₂ b = begin transport B (p ^-1) (transport B p b) 
               ≡⟨ lemma-2-3-9 {A} {B} {x} {y} {x} p (p ^-1) b ⟩ 
                  transport B (p · p ^-1) b 
               ≡⟨ cong (λ s → transport B s b) (rinv p) ⟩ 
                  (b ∎)

isequiv : {A B : Set} -> (f : A -> B) -> Set
isequiv {A} {B} f = (Σ (B → A) (λ g → (f ∘ g) ~ id)) × (Σ (B → A) (λ h → (h ∘ f) ~ id))

_≅_ : (A B : Set) -> Set
A ≅ B = Σ (A → B) isequiv -- woo!

qiIsEquiv : {A B : Set} -> (f : A -> B) -> quasi-inverse f -> isequiv f
qiIsEquiv f (g , p1 , p2) = (g , p1) , g , p2

equivIsQi : {A B : Set} -> (f : A -> B) -> isequiv f -> quasi-inverse f
equivIsQi f ((g , α) , h , β)= g , α , β' where
  γ : g ~ h
  γ x = begin g x 
           ≡⟨ sym (β (g x)) ⟩
              h (f (g x)) 
           ≡⟨ cong h (α x) ⟩ 
              (h x ∎) 


  β' : (g ∘ f) ~ id
  β' x = γ (f x) · β x

eqInv : {A B : Set} -> A ≅ B -> B ≅ A
eqInv (f , fequiv) with equivIsQi f fequiv 
eqInv (f , fequiv) | g , p₁ , p₂ = g , (f , p₂) , f , p₁
-- 
