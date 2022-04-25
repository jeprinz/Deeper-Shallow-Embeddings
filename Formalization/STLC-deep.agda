data Type : Set where
  _⇒_ : Type → Type → Type
  base : Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data Var : (Γ : Ctx) → Type → Set where
  same : ∀{Γ T} → Var (Γ , T) T
  next : ∀{Γ T A} → Var Γ A → Var (Γ , T) A

data Term : Ctx → Type → Set where
  var : ∀{Γ T} → (icx : Var Γ T) → Term Γ T
  lambda : ∀{Γ A B} → Term (Γ , A) B
    → Term Γ (A ⇒ B)
  app : ∀{Γ A B} → Term Γ (A ⇒ B)
    → Term Γ A → Term Γ B
  ⋆ : ∀{Γ} → Term Γ base
