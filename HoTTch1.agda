{-# OPTIONS --without-K #-}
module HoTTch1 where

module MyProd where
  data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

  ind : {A B : Set} -> (C : A × B -> Set) -> ((a : A) -> (b : B) -> C (a , b)) -> (x : A × B) -> C x
  ind C f (x , x₁) = f x x₁

module MyUnit where
  record ⊤ : Set where
    constructor tt 

  ind : (C : ⊤ -> Set) -> C tt -> (x : ⊤) -> C x
  ind C p tt = p

module MySum where
  data Σ (A : Set) (B : A -> Set) : Set where
    _,_ : (a : A) -> (B a) -> Σ A B

  ind : {A : Set} {B : A -> Set} -> (C : (Σ A B) -> Set)
           -> ((a : A) -> (b : B a) -> C (a , b)) -> (p : Σ A B) -> C p
  ind C f (a , x) = f a x  
 
  pr₁ : {A : Set} {B : A -> Set} -> Σ A B -> A
  pr₁ (a , x) = a
 
  pr₂ : {A : Set} {B : A -> Set} -> (p : Σ A B) -> B (pr₁ p)
  pr₂ (a , x) = x

  -- damn these types are easier to read in Agda

  ac : {A B : Set} {R : A -> B -> Set} -> ((a : A) -> Σ B (λ y -> R a y)) -> (Σ (A -> B) (λ f -> (x : A) -> R x (f x)))
  ac g = (λ x → pr₁ (g x)) , (λ a → pr₂ (g a))

module MyCo where

  data _+_ (A B : Set) : Set where
    inl : A -> A + B
    inr : B -> A + B

  data ⊥ : Set where

  rec⊥ : {C : Set} -> ⊥ -> C
  rec⊥ ()

  ind : {A B : Set} -> (C : A + B -> Set) -> ((a : A) -> C (inl a)) -> ((b : B) -> C (inr b)) -> (p : A + B) -> C p
  ind C l r (inl x) = l x
  ind C l r (inr x) = r x

  open import Data.Product
  ex : {A B : Set} -> (A -> ⊥) × (B -> ⊥) -> A + B -> ⊥
  ex (a⊥ , b⊥) (inl x) = a⊥ x
  ex (a⊥ , b⊥) (inr x) = b⊥ x

  ex2 : {A B : Set} -> (A + B -> ⊥) -> (A -> ⊥) × (B -> ⊥)
  ex2 f = (λ a → f (inl a)) , (λ b → f (inr b))

module MyBool where

  open MySum hiding (ind)
  open import Level

  data _≡_ {A : Set} : A -> A -> Set where
   refl : (a : A) -> a ≡ a

  data Bool : Set where
     True : Bool
     False : Bool

  ind : {i : Level} (C : Bool -> Set i) -> C True -> C False -> (a : Bool) -> C a
  ind C ct cf True = ct
  ind C ct cf False = cf

  rec : {i : Level} (C : Set i) -> C -> C -> Bool -> C
  rec C ct cf True = ct
  rec C ct cf False = cf

  _+_ : Set -> Set -> Set
  A + B = Σ Bool (λ x → rec Set A B x)

  inl : {A B : Set} -> A -> A + B
  inl a = True , a

  inr : {A B : Set} -> B -> A + B
  inr b = False , b

  ind+ : {A B : Set} -> (C : A + B -> Set) -> ((a : A) -> C (inl a)) -> ((b : B) -> C (inr b)) -> (p : A + B) -> C p
  ind+ C l r (True , x) = l x
  ind+ C l r (False , x) = r x

  ex : (x : Bool) -> (x ≡ True) + (x ≡ False)
  ex True = inl (refl True)
  ex False = inr (refl False)

  ex' : (x : Bool) -> (x ≡ True) + (x ≡ False)
  ex' x = ind (λ y → (y ≡ True) + (y ≡ False)) (inl (refl True)) (inr (refl False)) x

module MyIden where
  
  open import Level
  data _≡_ {A : Set} : A -> A -> Set where
    refl : (a : A) -> a ≡ a

  ind : {i : Level} {A : Set} -> (C : (x y : A) -> x ≡ y -> Set i)
                   -> ((a : A) -> C a a (refl a)) -> (x y : A) -> (p : x ≡ y) -> C x y p
  ind C rs .y y (refl .y) = rs y

  ind* : {i : Level} {A : Set} {a : A} -> (C : (x : A) -> a ≡ x -> Set i)
                   -> (C a (refl a)) -> (x : A) -> (p : a ≡ x) -> C x p
  ind* C r x (refl .x) = r

  ind' :  {i : Level} {A : Set} -> (C : (x y : A) -> x ≡ y -> Set i)
                   -> ((a : A) -> C a a (refl a)) -> (x y : A) -> (p : x ≡ y) -> C x y p
  ind' C f x y p = ind* (C x) (f x) y p

-- so what we have here is that we've got 

  ind*' : {i : Level} {A : Set} {a : A} -> (C : (x : A) -> a ≡ x -> Set i)
                   -> (C a (refl a)) -> (x : A) -> (p : a ≡ x) -> C x p
  ind*' {i} {A} {a} C r x p = {!!}
           where D : (x y : A) -> (x ≡ y) -> Set (suc i)
                 D x y p = (C₁ : (z : A) → x ≡ z → Set i) → C₁ x (refl x) → C₁ y p
  -- okay I don't get this, even with using universes it doesn't entirely make sense
  -- is this a place where cumulativity matters so that we can bump up the level of C?

