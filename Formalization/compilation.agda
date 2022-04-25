{-# OPTIONS --cumulativity #-}
open import Deeper-Shallow-Embedding
open import Data.String hiding (show)
open import Data.Nat
open import Data.Nat.Show

_-_ : ℕ -> ℕ -> ℕ
zero  - m     = zero
suc n - zero  = suc n
suc n - suc m = n - m

len : ∀{sΓ} → Context sΓ → ℕ
len ∅ = 0
len (Γ , T) = 1 + (len Γ)

index : ∀{sΓ Γ T s} → Var {sΓ} Γ T s → ℕ
index same = 0
index (next x) = 1 + (index x)

compileToJs : ∀{sΓ Γ T s} → Term {sΓ} Γ T s → String
compileToJs {sΓ} {Γ} (lambda e)
  = "function(x" ++ (show (len Γ)) ++ ")"
    ++ "{" ++ compileToJs e ++ "}"
compileToJs {sΓ} {Γ} (var x)
  = "x" ++ (show ((len Γ) - (index x)))
compileToJs (app e₁ e₂)
  = "(" ++ (compileToJs e₁) ++ "
    " ++ (compileToJs e₂) ++ ")"
compileToJs (Π₀ e₁ e₂) = "null"
compileToJs (Π₁ e₁ e₂) = "null"
compileToJs U₀ = "null"
compileToJs U₁ = "null"
compileToJs (Lift e) = compileToJs e
compileToJs (lift e) = compileToJs e
compileToJs (lower e) = compileToJs e
