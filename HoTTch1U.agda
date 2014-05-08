{-# OPTIONS --without-K --type-in-type #-}

module HoTTch1U where

data _≡_ {A : Set} : A -> A -> Set where
  refl : (a : A) -> a ≡ a

ind : {A : Set} -> (C : (x y : A) -> x ≡ y -> Set)
                   -> ((a : A) -> C a a (refl a)) -> (x y : A) -> (p : x ≡ y) -> C x y p
ind C rs .y y (refl .y) = rs y

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

