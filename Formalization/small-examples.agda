{-# OPTIONS --cumulativity #-}
open import Data.Nat
open import Data.Nat.Show
open import Deeper-Shallow-Embedding
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.String hiding (show)
open import Data.Fin hiding (_+_ ; _-_ ; lift)
import Dep-Thy-shallow as S

extract : ∀{sΓ Γ T t} → Term {sΓ} Γ T t → S.Term sΓ T
extract {sΓ} {Γ} {T} {t} e = t

consistency : ∀{t} → Term {S.∅} ∅ (λ _ → ⊥) t → ⊥
consistency e = (extract e) tt

-- Or, if you prefer working with church encoding:
consistency2 : ∀{t} → Term {S.∅} ∅ (S.Π₁ S.U₀ (S.var (S.same))) t → ⊥
consistency2 e = ((extract e) tt) ⊥

idU : Term ∅ (S.Π₁ S.U₀ S.U₀) _
idU = lambda (var same)

id : Term ∅ (S.Π₁ S.U₀ (S.Lift (S.Π₀ (S.var S.same) (S.var (S.next S.same))))) _
id = lambda (lift (lambda (var same)))

one : Term ∅ (λ _ → (X Y : Set) → (X → Y) → X → Y) _
one = lambda (lambda (lambda (lambda (app (var (next same)) (var same)))))
