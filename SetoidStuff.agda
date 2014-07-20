module SetoidStuff where

open import Data.List
open import Relation.Binary
open import Relation.Binary.Core
open import Level

listRel' : {A : Set} -> List A -> List A -> Set
listRel' l1 l2 = length l1 ≡ length l2

-- huh so this is actually really interesting because basically we don't have much inductive
-- structure here in listRel as defined but if we /include/ the inductive structure maybe we'll have more to work with?

data listRel (A : Set) : List A -> List A -> Set where
  nils : listRel A [] []
  cons : {a b : A} {l1 l2 : List A} -> listRel A l1 l2 -> listRel A (a ∷ l1) (b ∷ l2)

{-
lemmer : {A : Set} -> (a b : A) -> (l1 l2 : List A) -> listRel' (a ∷ l1) (b ∷ l2) -> listRel' l1 l2
lemmer a b [] [] p = refl
lemmer a b [] (x ∷ l2) ()
lemmer a b (x ∷ l1) [] ()
lemmer a b (x ∷ l1) (x₁ ∷ l2) p = {!!}

equivIsh-1 : {A : Set} -> (l1 l2 : List A) -> listRel' l1 l2 -> listRel A l1 l2
equivIsh-1 [] [] p1 = nils
equivIsh-1 [] (x ∷ l2) ()
equivIsh-1 (x ∷ l1) [] ()
equivIsh-1 (x ∷ l1) (x₁ ∷ l2) p1 = cons {!equivIsh-1 l1 l2!}
-}

listRelRefl' : {A : Set} -> (l1 : List A) -> listRel A l1 l1
listRelRefl' [] = nils
listRelRefl' (x ∷ l1) = cons (listRelRefl' l1)

listRelRefl : {A : Set} -> Reflexive (listRel A)
listRelRefl = λ {A} {x} → listRelRefl' x

listRelTrans' : {A : Set} -> {l1 l2 l3 : List A}
                          -> listRel A l1 l2 -> listRel A l2 l3 -> listRel A l1 l3
listRelTrans' nils nils = nils
listRelTrans' (cons p1) (cons p2) = cons (listRelTrans' p1 p2)

listRelTrans : {A : Set} -> Transitive (listRel A)
listRelTrans = listRelTrans'

listRelSym : {A : Set} -> Symmetric (listRel A)
listRelSym nils = nils
listRelSym (cons p) = cons (listRelSym p)

listEquiv : {A : Set} -> IsEquivalence (listRel A)
listEquiv = record { refl = (listRelRefl);
                         trans = (listRelTrans);
                         sym = (listRelSym) }


listSetoid : {A : Set} -> Setoid zero zero
listSetoid {A} = record {isEquivalence = (listEquiv {A = A})}

{- 
  So what's a notion of equivalence between setoids?
  I'm guessing that you have a pair of maps back and forth such that the equivalence
  relation is respected?

  
-}


module NatEquiv where

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality


  aintEmpty : (A : Set) -> Set
  aintEmpty A = A

  listToNat : {A : Set} -> List A -> ℕ
  listToNat = length

  natToList : {A : Set} -> aintEmpty A -> ℕ -> List A
  natToList a ℕ.zero = []
  natToList a (ℕ.suc n) = a ∷ natToList a n

  isQuasiInverseish-1 : {A : Set} -> (a : aintEmpty A) -> (l : List A) -> listRel A (natToList a (listToNat l)) l
  isQuasiInverseish-1 a [] = nils
  isQuasiInverseish-1 a (x ∷ l) = cons (isQuasiInverseish-1 a l)

  isQuasiInverseish-2 : {A : Set} -> (a : aintEmpty A) -> (n : ℕ) -> listToNat (natToList a n) ≡ n
  isQuasiInverseish-2 a ℕ.zero = refl
  isQuasiInverseish-2 a (ℕ.suc n) = cong ℕ.suc (isQuasiInverseish-2 a n)

  -- tada! if lists are only seen "up-to-length" then they're just the natural numbers. A rather obvious mathematical fact but a decent test at least
