{-# OPTIONS --cumulativity #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Maybe

open import Deeper-Shallow-Embedding
import Dep-Thy-shallow as S

data VarData : ∀{sΓ} → Context sΓ → Set where
  ∅ : VarData ∅
  _,_ : ∀{sΓ} → {Γ : Context sΓ} → {T : S.Type sΓ}
    → VarData Γ → Bool → VarData (Γ , T)

data Check : ∀{sΓ} → {Γ : Context sΓ}
  → VarData Γ → VarData Γ → VarData Γ → Set j where
  ∅ : Check ∅ ∅ ∅
  consLeft : ∀{sΓ} → {Γ : Context sΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ} → (T : S.Type sΓ)
    → Check Γ₁ Γ₂ Γ₃ → Check {_} {Γ , T} (Γ₁ , true) (Γ₂ , false) (Γ₃ , true)
  consRight : ∀{sΓ} → {Γ : Context sΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ} → (T : S.Type sΓ)
    → Check Γ₁ Γ₂ Γ₃ → Check {_} {Γ , T} (Γ₁ , false) (Γ₂ , true) (Γ₃ , true)
  consNeither : ∀{sΓ} → {Γ : Context sΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ} → (T : S.Type sΓ)
    → Check Γ₁ Γ₂ Γ₃ → Check {_} {Γ , T} (Γ₁ , false) (Γ₂ , false) (Γ₃ , false)

noneVars : ∀{sΓ} → {Γ : Context sΓ} → VarData Γ
oneVars : ∀{aΓ T t} → (Γ : Context aΓ) → Var Γ T t → VarData Γ
check : ∀{aΓ} → {Γ : Context aΓ} → (vd₁ vd₂ : VarData Γ)
  → Maybe (Σ {j} {j} (VarData Γ) (λ vd₃ → Check vd₁ vd₂ vd₃))

check ∅ ∅ = just (∅ , ∅)
check (vd₁ , x) (vd₂ , x₁) with check vd₁ vd₂
check (vd₁ , b₁) (vd₂ , b₂) | nothing = nothing
check (vd₁ , false) (vd₂ , false) | just (vd₃ , c) = just ((vd₃ , false) , consNeither _ c)
check (vd₁ , false) (vd₂ , true) | just (vd₃ , c) = just ((vd₃ , true) , consRight _ c)
check (vd₁ , true) (vd₂ , false) | just (vd₃ , c) = just ((vd₃ , true) , consLeft _ c)
check (vd₁ , true) (vd₂ , true) | just (vd₃ , c) = nothing

noneVars {_}  {∅} = ∅
noneVars {_}  {Γ , T} = noneVars , false

oneVars .(_ , _) same = noneVars , true
oneVars .(_ , _) (next x) = oneVars _ x , false

data AffineTerm : {sΓ : S.Ctx} → (Γ : Context sΓ) → VarData Γ
  → (T : S.Type sΓ) → S.Term sΓ T → Set j where
  lambda : {b : Bool} → {sΓ : S.Ctx} → {Γ : Context sΓ} → {vd : VarData Γ}
    → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s}
    → AffineTerm (Γ , A) (vd , b) B s → AffineTerm Γ vd (S.Π A B) (S.lambda s)
  var : {sΓ : S.Ctx} → {Γ : Context sΓ} → {T : S.Type sΓ} → {s : S.Term sΓ T}
    → (x : Var Γ T s) → AffineTerm {sΓ} Γ (oneVars Γ x) T s
  app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ}
      → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
      → AffineTerm Γ Γ₁ (S.Π A B) s₁ → (x : AffineTerm Γ Γ₂ A s₂)
      → Check Γ₁ Γ₂ Γ₃
      → AffineTerm Γ Γ₃ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
  Π₀ : {b : Bool} → {sΓ : S.Ctx} → {Γ : Context sΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ}
    → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
    → AffineTerm Γ Γ₁ S.U₀ s₁ → AffineTerm (Γ , s₁) (Γ₂ , b) S.U₀ s₂
    → Check Γ₁ Γ₂ Γ₃
    → AffineTerm Γ Γ₃ S.U₀ (S.Π₀ s₁ s₂)
  Π₁ : {b : Bool} → {sΓ : S.Ctx} → {Γ : Context sΓ} → {Γ₁ Γ₂ Γ₃ : VarData Γ}
    → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
    → AffineTerm Γ Γ₁ S.U₁ s₁ → AffineTerm (Γ , s₁) (Γ₂ , b) S.U₁ s₂
    → Check Γ₁ Γ₂ Γ₃
    → AffineTerm Γ Γ₃ S.U₁ (S.Π₁ s₁ s₂)
  U₀ : ∀{sΓ Γ} → AffineTerm {sΓ} Γ (noneVars) S.U₁ S.U₀
  U₁ : ∀{sΓ Γ} → AffineTerm {sΓ} Γ (noneVars) S.U₂ S.U₁
  Lift : ∀{sΓ Γ s vd} → AffineTerm {sΓ} Γ vd S.U₀ s → AffineTerm Γ vd S.U₁ (S.Lift s)
  lift : ∀{sΓ Γ vd} → {T : S.Type₀ sΓ} → {s : S.Term sΓ T}
    → AffineTerm {sΓ} Γ vd T s → AffineTerm Γ vd (S.Lift T) (S.lift s)
  lower : ∀{sΓ Γ vd} → {T : S.Type₀ sΓ} → {s : S.Term sΓ T}
    → AffineTerm Γ vd (S.Lift T) (S.lift s) → AffineTerm {sΓ} Γ vd T s

checkAffine : ∀{sΓ Γ T t} → Term {sΓ} Γ T t
  → Maybe (Σ {j} {j} (VarData Γ) (λ vd → AffineTerm {sΓ} Γ vd T t))
checkAffine (lambda e) with checkAffine e
... | nothing = nothing
... | just ((vd , false) , Ae) = just (vd , lambda Ae) -- would be nothing if linear
... | just ((vd , true) , Ae) = just (vd , lambda Ae)
checkAffine (var icx) = just (oneVars _ icx , var icx)
checkAffine (app e₁ e₂) with checkAffine e₁ | checkAffine e₂
... | nothing | res2 = nothing
... | just x | nothing = nothing
... | just (vd₁ , Ae₁) | just (vd₂ , Ae₂) with check vd₁ vd₂
... | nothing = nothing
... | just (vd₃ , c) = just (vd₃ , app Ae₁ Ae₂ c)
checkAffine (Π₀ e₁ e₂) with checkAffine e₁ | checkAffine e₂
... | nothing | res2 = nothing
... | just x | nothing = nothing
... | just (vd₁ , ae₁) | just ((vd₂ , b) , ae₂) with check vd₁ vd₂
... | nothing = nothing
... | just (vd , c) = just (vd , Π₀ ae₁ ae₂ c)
checkAffine (Π₁ e₁ e₂) with checkAffine e₁ | checkAffine e₂
... | nothing | res2 = nothing
... | just x | nothing = nothing
... | just (vd₁ , ae₁) | just ((vd₂ , b) , ae₂) with check vd₁ vd₂
... | nothing = nothing
... | just (vd , c) = just (vd , Π₁ ae₁ ae₂ c)
checkAffine U₀ = just (noneVars ,  U₀)
checkAffine U₁ = just (noneVars ,  U₁)
checkAffine (Lift e) with checkAffine e
... | nothing = nothing
... | just (vd , e') = just (vd , Lift e')
checkAffine (lift e) with checkAffine e
... | nothing = nothing
... | just (vd , e') = just (vd , lift e')
checkAffine (lower e) with checkAffine e
... | nothing = nothing
... | just (vd , e') = just (vd , lower e')

-- Some examples

ex1 : AffineTerm ∅ ∅ (λ _ → (Set → Set)) _
ex1 = lambda (var same)

ex1' : Term ∅ (λ _ → (Set → Set)) _
ex1' = lambda (var same)

test1 : checkAffine ex1' ≡ just (_ , ex1)
test1 = refl

ex2 : Term ∅ (λ _ → (X : Set) → X → X) _
ex2 = lambda (lambda (var same))

test2 : checkAffine ex2 ≡ just (_ , lambda (lambda (var same)))
test2 = refl
