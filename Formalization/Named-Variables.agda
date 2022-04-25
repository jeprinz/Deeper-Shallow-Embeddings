{-# OPTIONS --cumulativity #-}

open import Data.Product hiding (map)
open import Agda.Primitive
open import Data.Unit hiding (_≟_)
open import Data.String
open import Data.Maybe
open import Data.Bool hiding (_≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function

import Dep-Thy-shallow as S

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

data Context : S.Ctx → Set j where
  ∅ : Context S.∅
  _,_∷_ : ∀{sΓ} → Context sΓ → String → (T : S.Type sΓ) → Context (S.cons sΓ T)

data Var : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → (S.Term sΓ T) → Set j where
  same : ∀{sΓ T name} → {Γ : Context sΓ} → Var (Γ , name ∷ T) (S.weakenT T) S.same
  next : ∀{sΓ Γ T A s name} → Var {sΓ} Γ A s → Var (Γ , name ∷ T) (S.weakenT A) (S.next s)

findVar : ∀{sΓ} → (Γ : Context sΓ) → String
  → Maybe (Σ {j} {j} (Σ {j} {i} (S.Type sΓ) (S.Term sΓ)) (λ (T , t) → Var Γ T t))
findVar ∅ name = nothing
findVar (Γ , a ∷ A) name
  = if  ⌊ name ≟ a ⌋
    then just {j} ((S.subType (S.weaken1ren A) A , S.same) , same)
    else map
      (λ ((T , t) , x) → (S.subType (S.weaken1ren A) T , S.subTerm (S.weaken1ren A) T t) , next x)
      (findVar Γ name)

resultType : ∀{sΓ} → (Γ : Context sΓ) → String → S.Type sΓ
resultType Γ name with findVar Γ name
... | nothing = λ _ → ⊤
... | just ((T , t) , x) = T

resultTerm : ∀{sΓ} → (Γ : Context sΓ) → (name : String) → S.Term sΓ (resultType Γ name)
resultTerm Γ name with findVar Γ name
... | nothing = λ _ → tt
... | just ((T , t) , x) = t

data Term : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → S.Term sΓ T → Set j where
  var : ∀{sΓ} → {Γ : Context sΓ} → (name : String)
    → Term Γ (resultType Γ name) (resultTerm Γ name)
  lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)}
    → ∀{s} → (name : String) → Term (Γ , name ∷ A) B s → Term Γ (S.Π A B) (S.lambda s)
  app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
      → Term Γ (S.Π A B) s₁ → (x : Term Γ A s₂)
      → Term Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
  Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
    → (name : String)
    → (A : Term Γ S.U₀ s₁)
    → (B : Term (Γ , name ∷ s₁) S.U₀ s₂)
    → Term Γ S.U₀ (S.Π₀ s₁ s₂)
  Π₁ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
    → (name : String)
    → (A : Term Γ S.U₁ s₁)
    → (B : Term (Γ , name ∷ s₁) S.U₁ s₂)
    → Term Γ S.U₁ (S.Π₁ s₁ s₂)
  U₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → Term {sΓ} Γ S.U₁ S.U₀
  U₁ : ∀{sΓ Γ} → Term {sΓ} Γ S.U₂ S.U₁
  Lift : ∀{sΓ Γ s} → Term {sΓ} Γ S.U₀ s → Term Γ S.U₁ (S.Lift s)
  lift : ∀{sΓ Γ} → {T : S.Type₀ sΓ} → {s : S.Term sΓ T}
    → Term {sΓ} Γ T s → Term Γ (S.Lift T) (S.lift s)
  lower : ∀{sΓ Γ} → {T : S.Type₀ sΓ} → {s : S.Term sΓ T}
    → Term Γ (S.Lift T) (S.lift s) → Term {sΓ} Γ T s

example : Term ∅ (λ _ → (X : Set) → X → X) _
example = lambda "X" (lambda "x" (var "x"))
