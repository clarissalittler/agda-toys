module STLC where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Data.List
open import Data.Product

data Ty : Set where
  TyNat : Ty
  TyArr : Ty -> Ty -> Ty

Env : Set
Env = List Ty

data Var : Env -> Ty -> Set where
  zvar : {Γ : Env}{t : Ty} -> Var (t ∷ Γ) t
  svar : {Γ : Env}{t t' : Ty} -> Var Γ t -> Var (t' ∷ Γ) t


data Lam (Γ : Env) : Ty -> Set where
  LVar : {t : Ty} -> Var Γ t -> Lam Γ t
  LZero : Lam Γ TyNat
  LSucc : Lam Γ TyNat -> Lam Γ TyNat
  LApp : {t1 t2 : Ty} -> Lam Γ (TyArr t1 t2) -> Lam Γ t1 -> Lam Γ t2
  LAbs : {t1 t2 : Ty} -> Lam (t1 ∷ Γ) t2 -> Lam Γ (TyArr t1 t2)

sub : Env -> Env -> Set
sub Γ Γ' = {t : _} -> Var Γ t -> Lam Γ' t

idSub : ∀ {Γ} -> sub Γ Γ
idSub = λ v -> LVar v

consSub : ∀ {Γ Γ' t} -> Lam Γ' t -> sub Γ Γ' -> sub (t ∷ Γ) Γ'
consSub e s zvar = e
consSub e s (svar y) = s y

<<_>> : ∀ {Γ t} -> Lam Γ t -> sub (t ∷ Γ) Γ
<< e >> = consSub e idSub

lift-var : {Γ : Env}{t t' : Ty} -> (Γ' : Env) -> Var (Γ' ++ Γ) t -> Var (Γ' ++ [ t' ] ++ Γ) t
lift-var [] v = svar v
lift-var {Γ} {t} (.t ∷ xs) zvar = zvar
lift-var (x ∷ xs) (svar y) = svar (lift-var xs y) 

lift : {Γ : Env}{t t' : Ty} -> (Γ' : Env) -> Lam (Γ' ++ Γ) t -> Lam (Γ' ++ [ t' ] ++ Γ) t
lift γ (LVar y) = LVar (lift-var γ y)
lift γ LZero = LZero
lift γ (LSucc y) = LSucc (lift γ y)
lift γ (LApp y y') = LApp (lift γ y) (lift γ y')
lift {Γ} {TyArr t1 t2} γ (LAbs y) = LAbs (lift (t1 ∷ γ) y)

subLift : ∀ {Γ Γ' t} -> sub Γ Γ' -> sub (t ∷ Γ) (t ∷ Γ')
subLift s zvar = LVar zvar
subLift s (svar y) = lift [] (s y)

subExp : ∀ {Γ Γ' t} -> sub Γ Γ' -> Lam Γ t -> Lam Γ' t
subExp s (LVar y) = s y
subExp s LZero = LZero
subExp s (LSucc y) = LSucc (subExp s y)
subExp s (LApp y y') = LApp (subExp s y) (subExp s y')
subExp s (LAbs y) = LAbs (subExp (subLift s) y)

subβ : ∀ {Γ ty₁ ty₂} -> Lam (ty₁ ∷ Γ) ty₂ -> Lam Γ ty₁ -> Lam Γ ty₂
subβ t1 t2 = subExp << t2 >> t1

data Val {Γ : Env} : {t : Ty} -> Lam Γ t -> Set where
  vAbs : {ty₁ ty₂ : Ty} -> {l : Lam (ty₁ ∷ Γ) ty₂} -> Val (LAbs l)

data _β_ {Γ : Env} : {t : Ty} -> Lam Γ t -> Lam Γ t -> Set where
  app₁ : {ty₁ ty₂ : Ty} {t₁ t₂ : Lam Γ ty₁} {l : Lam Γ (TyArr ty₁ ty₂)} -> t₁ β t₂ -> LApp l t₁ β LApp l t₂
  app₂ : {ty₁ ty₂ : Ty} {v : Lam Γ ty₁} {l₁ l₂ : Lam Γ (TyArr ty₁ ty₂)} -> Val v -> l₁ β l₂ -> LApp l₁ v β LApp l₂ v
  appλ : {ty₁ ty₂ : Ty} {v : Lam Γ ty₁} {l : Lam (ty₁ ∷ Γ) ty₂} -> Val v -> LApp (LAbs l) v β (subβ l v)
