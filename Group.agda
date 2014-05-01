module Group where

open import Relation.Binary.PropositionalEquality
open import Data.Product

-- I think this basically the end of this file, since I'm getting bored with it all. If only I still had a copy of Herstein's book maybe I'd try proving stuff still.

record Group (A : Set) : Set where
  constructor G
  field
    e : A
    _⋆_ : A -> A -> A
    li : {a : A} -> e ⋆ a ≡ a
    ri : {a : A} -> a ⋆ e ≡ a
    inv : A -> A
    linv : (a : A) -> (inv a) ⋆ a ≡ e
    rinv : (a : A) -> a ⋆ (inv a) ≡ e
    assoc : {a b c : A} -> (a ⋆ b) ⋆ c ≡ a ⋆ (b ⋆ c)

module GroupTh {A : Set} (G : Group A) where
  open ≡-Reasoning

  e : A
  e = Group.e G
  
  _⋆_ : A -> A -> A
  x ⋆ y = (G Group.⋆ x) y

  inv : A -> A
  inv = Group.inv G

  ex1 : e ⋆ e ≡ e
  ex1 = Group.li G
  
  ex2 : (e' : A) -> ((a : A) -> e' ⋆ a ≡ a) -> ((a : A) -> a ⋆ e' ≡ a) -> e' ≡ e
  ex2 e' li' ri' = begin e' 
                      ≡⟨ sym (Group.ri G) ⟩ 
                         e' ⋆ e 
                      ≡⟨ li' e ⟩ 
                         (e ∎) -- wow, that was really painful at first but hopefully it'll get easier to think in that syntax. It's cute though, I'll give them that much. So, hey, at least that means that I've now figured out how to use the damn syntax /plus/ hey we also proved one of the first things you learn how to do in an algebra class. 

  ex3 : (a a- : A) -> a ⋆ a- ≡ e -> a- ⋆ a ≡ e -> a- ≡ inv a
  ex3 a a- rinv- linv- = begin a- 
                                ≡⟨ sym (Group.li G) ⟩ 
                              e ⋆ a- 
                                ≡⟨ cong (λ x → x ⋆ a-) (sym (Group.linv G a)) ⟩ 
                              (inv a ⋆ a) ⋆ a- 
                                ≡⟨ Group.assoc G ⟩ 
                              inv a ⋆ (a ⋆ a-) 
                                ≡⟨ cong (λ x → inv a ⋆ x) rinv- ⟩ 
                              inv a ⋆ e 
                                ≡⟨ Group.ri G ⟩ 
                              (inv a ∎)

-- so that was uniqueness of the identity, so now let's try and prove that double negation is the identity

  ex4 : (a : A) -> inv (inv a) ≡ a
  ex4 a = sym (ex3 (inv a) a (Group.linv G a) (Group.rinv G a))

-- kinda neat that at least this proof is really simple given what we did in the previous exercise

module IntTest where
  open import Data.Integer  
  open import Data.Nat as ℕ using (ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_) 

  aux1 : (a : ℤ) -> + 0 + a ≡ a
  aux1 -[1+ n ] = refl
  aux1 (+ n) = refl

  blorp : (n : ℕ) -> n ℕ+ 0 ≡ n
  blorp ℕ.zero = refl
  blorp (ℕ.suc n) = cong ℕ.suc (blorp n)

  aux2 : (a : ℤ) -> a + (+ 0) ≡ a
  aux2 -[1+ n ] = refl
  aux2 (+ n) = cong (λ n₁ → + n₁) (blorp n)

  blech : (a : ℕ) -> a ⊖ a ≡ + 0
  blech ℕ.zero = refl
  blech (ℕ.suc a) = blech a

  aux3 : (a : ℤ) -> (- a) + a ≡ (+ 0)
  aux3 -[1+ n ] = blech n
  aux3 (+ ℕ.zero) = refl
  aux3 (+ ℕ.suc n) = blech n

  aux4 : (a : ℤ) -> a + (- a) ≡ (+ 0)
  aux4 -[1+ n ] = blech n
  aux4 (+ ℕ.zero) = refl
  aux4 (+ ℕ.suc n) = blech n

  aux5 : (a b c : ℤ) -> (a + b) + c ≡ a + (b + c)
  aux5 -[1+ n ] b c = {!!}
  aux5 (+ ℕ.zero) -[1+ n ] c = {!!}
  aux5 (+ ℕ.zero) (+ n) -[1+ n₁ ] = {!!}
  aux5 (+ ℕ.zero) (+ n) (+ n₁) = refl
  aux5 (+ ℕ.suc n) -[1+ n₁ ] c = {!!}
  aux5 (+ ℕ.suc n) (+ n₁) c = {!!}
-- ugh this is ugly basically because of how addition is defined on integers in Agda
-- I really don't feel like going through all the effort to do this proof tbh

  ex : Group ℤ
  ex = G (+ 0) _+_ (aux1 _) (aux2 _) -_ aux3  aux4 (λ {a} {b} {c} → aux5 a b c)

    
