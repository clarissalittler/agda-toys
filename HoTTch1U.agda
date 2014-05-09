{-# OPTIONS --without-K --type-in-type #-}
module HoTTch1U where

record ⊤ : Set where
  constructor tt 

ind⊤ : (C : ⊤ -> Set) -> C tt -> (x : ⊤) -> C x
ind⊤ C p tt = p

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> (B a) -> Σ A B

indΣ : {A : Set} {B : A -> Set} -> (C : (Σ A B) -> Set)
           -> ((a : A) -> (b : B a) -> C (a , b)) -> (p : Σ A B) -> C p
indΣ C f (a , x) = f a x  
 
pr₁ : {A : Set} {B : A -> Set} -> Σ A B -> A
pr₁ (a , x) = a
 
pr₂ : {A : Set} {B : A -> Set} -> (p : Σ A B) -> B (pr₁ p)
pr₂ (a , x) = x

_×_ : (A B : Set) -> Set
A × B = Σ A (λ _ -> B)

  -- damn these types are easier to read in Agda

ac : {A B : Set} {R : A -> B -> Set} -> ((a : A) -> Σ B (λ y -> R a y)) -> (Σ (A -> B) (λ f -> (x : A) -> R x (f x)))
ac g = (λ x → pr₁ (g x)) , (λ a → pr₂ (g a))

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

data ⊥ : Set where

rec⊥ : {C : Set} -> ⊥ -> C
rec⊥ ()

ind : {A B : Set} -> (C : A + B -> Set) -> ((a : A) -> C (inl a)) -> ((b : B) -> C (inr b)) -> (p : A + B) -> C p
ind C l r (inl x) = l x
ind C l r (inr x) = r x

ex : {A B : Set} -> (A -> ⊥) × (B -> ⊥) -> A + B -> ⊥
ex (a⊥ , b⊥) (inl x) = a⊥ x
ex (a⊥ , b⊥) (inr x) = b⊥ x

ex2 : {A B : Set} -> (A + B -> ⊥) -> (A -> ⊥) × (B -> ⊥)
ex2 f = (λ a → f (inl a)) , (λ b → f (inr b))

data _≡_ {A : Set} : A -> A -> Set where
  refl : (a : A) -> a ≡ a

ind≡ : {A : Set} -> (C : (x y : A) -> x ≡ y -> Set)
                   -> ((a : A) -> C a a (refl a)) -> (x y : A) -> (p : x ≡ y) -> C x y p
ind≡ C rs .y y (refl .y) = rs y

ind* : {A : Set} {a : A} -> (C : (x : A) -> a ≡ x -> Set)
                   -> (C a (refl a)) -> (x : A) -> (p : a ≡ x) -> C x p
ind* C r x (refl .x) = r

ind' :  {A : Set} -> (C : (x y : A) -> x ≡ y -> Set)
                   -> ((a : A) -> C a a (refl a)) -> (x y : A) -> (p : x ≡ y) -> C x y p
ind' C f x y p = ind* (C x) (f x) y p

-- so what we have here is that we've got 

ind*' : {A : Set} {a : A} -> (C : (x : A) -> a ≡ x -> Set)
                   -> (C a (refl a)) -> (x : A) -> (p : a ≡ x) -> C x p
ind*' {A} {a} C r x p = f a x p C r
        where D : (x y : A) -> (x ≡ y) -> Set
              D x y p = (C₁ : (z : A) → x ≡ z → Set) → C₁ x (refl x) → C₁ y p
              f : (x y : A) -> (p : x ≡ y) -> D x y p
              f .y y (refl .y) C₁ c = c

