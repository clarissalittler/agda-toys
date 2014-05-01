module STLC where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
open import Data.Product
open import Data.Sum

data Ty : Set where
  TyBool : Ty
  TyArr : Ty -> Ty -> Ty

Env : Set
Env = List Ty

data Var : Env -> Ty -> Set where
  zvar : {Γ : Env}{t : Ty} -> Var (t ∷ Γ) t
  svar : {Γ : Env}{t t' : Ty} -> Var Γ t -> Var (t' ∷ Γ) t


data Lam (Γ : Env) : Ty -> Set where
  LVar : {t : Ty} -> Var Γ t -> Lam Γ t
  LTrue : Lam Γ TyBool
  LFalse : Lam Γ TyBool
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
lift γ LTrue = LTrue
lift γ LFalse = LFalse
lift γ (LApp y y') = LApp (lift γ y) (lift γ y')
lift {Γ} {TyArr t1 t2} γ (LAbs y) = LAbs (lift (t1 ∷ γ) y)

subLift : ∀ {Γ Γ' t} -> sub Γ Γ' -> sub (t ∷ Γ) (t ∷ Γ')
subLift s zvar = LVar zvar
subLift s (svar y) = lift [] (s y)

subExp : ∀ {Γ Γ' t} -> sub Γ Γ' -> Lam Γ t -> Lam Γ' t
subExp s (LVar y) = s y
subExp s LTrue = LTrue
subExp s LFalse = LFalse
subExp s (LApp y y') = LApp (subExp s y) (subExp s y')
subExp s (LAbs y) = LAbs (subExp (subLift s) y)

subβ : ∀ {Γ ty₁ ty₂} -> Lam (ty₁ ∷ Γ) ty₂ -> Lam Γ ty₁ -> Lam Γ ty₂
subβ t1 t2 = subExp << t2 >> t1

data Val {Γ : Env} : {t : Ty} -> Lam Γ t -> Set where
  vAbs : {ty₁ ty₂ : Ty} -> (l : Lam (ty₁ ∷ Γ) ty₂) -> Val (LAbs l)
  vTrue : Val LTrue
  vFalse : Val LFalse

module CBV where
  data _β_ {Γ : Env} : {t : Ty} -> Lam Γ t -> Lam Γ t -> Set where
    app₁ : {ty₁ ty₂ : Ty} {t₁ t₂ : Lam Γ ty₁} {l : Lam Γ (TyArr ty₁ ty₂)} -> t₁ β t₂ -> LApp l t₁ β LApp l t₂
    app₂ : {ty₁ ty₂ : Ty} {v : Lam Γ ty₁} {l₁ l₂ : Lam Γ (TyArr ty₁ ty₂)} -> Val v -> l₁ β l₂ -> LApp l₁ v β LApp l₂ v
    appλ : {ty₁ ty₂ : Ty} {v : Lam Γ ty₁} {l : Lam (ty₁ ∷ Γ) ty₂} -> Val v -> LApp (LAbs l) v β (subβ l v)

  progress : {t : Ty} -> (l : Lam [] t) -> Val l ⊎ Σ (Lam [] t) (λ l' -> l β l')
  progress (LVar ())
  progress LTrue = inj₁ vTrue
  progress LFalse = inj₁ vFalse
  progress (LApp l₁ l₂) with progress l₂
  progress (LApp l₁ l₂) | inj₁ x with progress l₁
  progress (LApp .(LAbs l) l₂) | inj₁ v2 | inj₁ (vAbs l) = inj₂ (subβ l l₂ , appλ v2)
  progress (LApp l₁ l₂) | inj₁ x | inj₂ (l₁' , l₁β) = inj₂ (LApp l₁' l₂ , app₂ x l₁β)
  progress (LApp l₁ l₂) | inj₂ (l₂' , l₂β) = inj₂ (LApp l₁ l₂' , app₁ l₂β)
  progress (LAbs l) = inj₁ (vAbs l)

-- whoah, that was so much easier than I remember it being. Admittedly, that's the strongly typed syntax at work but /still/

module CBN where
  data _β_ {Γ : Env} : {t : Ty} -> Lam Γ t -> Lam Γ t -> Set where
    app : {ty₁ ty₂ : Ty} {l₁ l₂ : Lam Γ (TyArr ty₁ ty₂)} {x : Lam Γ ty₁} -> l₁ β l₂ -> LApp l₁ x β LApp l₂ x
    appλ : {ty₁ ty₂ : Ty} {x : Lam Γ ty₁} {l : Lam (ty₁ ∷ Γ) ty₂} -> LApp (LAbs l) x β (subβ l x)

  progress : {t : Ty} -> (l : Lam [] t) -> Val l ⊎ Σ (Lam [] t) (λ l' -> l β l')
  progress (LVar ())
  progress LTrue = inj₁ vTrue
  progress LFalse = inj₁ vFalse
  progress (LApp l l₁) with progress l
  progress (LApp .(LAbs l) l₁) | inj₁ (vAbs l) = inj₂ (subβ l l₁ , appλ)
  progress (LApp l l₁) | inj₂ (l' , lβ) = inj₂ (LApp l' l₁ , app lβ)
  progress (LAbs l) = inj₁ (vAbs l)

module Denotation where

  open import Data.Bool
  open import Data.Unit

  open CBV

  ⟦_⟧ty : Ty -> Set
  ⟦ TyBool ⟧ty = Bool
  ⟦ TyArr t t₁ ⟧ty = ⟦ t ⟧ty → ⟦ t₁ ⟧ty

  <[_]> : Env -> Set
  <[ [] ]> = ⊤
  <[ x ∷ γ ]> = ⟦ x ⟧ty × <[ γ ]>

  ⟦_⟧v_ : {Γ : Env} {t : Ty} -> Var Γ t -> <[ Γ ]> -> ⟦ t ⟧ty
  ⟦ zvar ⟧v (proj₁ , proj₂) = proj₁
  ⟦ svar v ⟧v γ = ⟦ v ⟧v proj₂ γ

  ⟦_⟧tm_ : {Γ : Env} {t : Ty} -> Lam Γ t -> <[ Γ ]> -> ⟦ t ⟧ty
  ⟦ LVar x ⟧tm γ = ⟦ x ⟧v γ
  ⟦ LTrue ⟧tm γ = true
  ⟦ LFalse ⟧tm γ = false
  ⟦ LApp l l₁ ⟧tm γ = (⟦ l ⟧tm γ) (⟦ l₁ ⟧tm γ)
  ⟦ LAbs l ⟧tm γ = λ z → ⟦ l ⟧tm (z , γ) 
-- I used auto for all of these...and it worked....that's HORRIFYING. Are the terms really just that forced by the types?

-- of course, now I want to prove that the β reduction agrees with the denotational semantics. This might be a bit tougher. In fact, it might need functional extensionality.
-- Needing functional extensionality is "okay" in a sense. It's not inconsistent, just not "in the spirit of things" if I understand correctly. 

-- Okay so we've got the two easy cases here, but we need to do the case of substitution which isn't as obvious to me

-- I think we need something like
-- ⟦ l ⟧tm (v , γ) ≡ ⟦ subβ l v ⟧ γ

  subResp : {Γ : Env} {t₁ t₂ : Ty} -> (l : Lam (t₁ ∷ Γ) t₂) -> (a : Lam Γ t₁) -> (γ : <[ Γ ]>) -> ⟦ l ⟧tm ( ⟦ a ⟧tm γ , γ) ≡ ⟦ subβ l a ⟧tm γ
  subResp l a γ = {!!} -- this is going to be the scary part

  semResp : {Γ : Env} (t : Ty) -> (l l' : Lam Γ t) -> l β l' -> (γ : <[ Γ ]>) -> ⟦ l ⟧tm γ ≡ ⟦ l' ⟧tm γ
  semResp t .(LApp l t₁) .(LApp l t₂) (app₁ {ty₁} {.t} {t₁} {t₂} {l} p) γ = cong (λ x → (⟦ l ⟧tm γ) x) (semResp ty₁ t₁ t₂ p γ)
  semResp t .(LApp l₁ v) .(LApp l₂ v) (app₂ {ty₁} {.t} {v} {l₁} {l₂} x p) γ = cong (λ f → f (⟦ v ⟧tm γ)) (semResp (TyArr ty₁ t) l₁ l₂ p γ)
  semResp t .(LApp (LAbs l) v) .(subExp (consSub v LVar) l) (appλ {ty₁} {.t} {v} {l} x) γ = subResp l v γ --woohoo so subResp is exactly what we need
