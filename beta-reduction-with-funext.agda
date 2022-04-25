{-# OPTIONS --without-K #-}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function

----------------------------- Function Extentionality --------------------------

{-
In order to implement function extentionality, I use two postulates and a
rewrite rule. This gives the necessary computation for this particular purpose.

I have also turned off Axiom-K, just to ensure compatibility with any potential
type theory with computational univalence.
-}

postulate
  funExt : ∀{l} {A B : Set l} {f g : A → B}
     → ((x : A) → f x ≡ g x) → f ≡ g
  funExtElim : ∀{l} {A B : Set l} {f : A → B}
     → funExt {l} {A} {B} {f} {f} (λ x → refl) ≡ refl

{-# REWRITE funExtElim #-}

happly : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
            → f ≡ g → ((x : A) → f x ≡ g x)
happly refl x = refl

--------------------------------------------------------------------------------
-- Definition of typecodes.

{-
Really, the way that we would like to be able to define TypeCodes is with a function
Which inducts on the level (n : ℕ), and then outputs a datatype. This is different
from a type parametrized by (n : ℕ). However, Agda only allows datatype definitions
at the top level.

The trick to do this in Agda therefore is to write two cases for TypeCode:
The zero case TypeCode₀, and the successor case TypeCodeₙ₊₁.
The latter is in a module which takes the induction hypothesis.

Finally, TypeCode does induction on n and uses TypeCode₀ and TypeCodeₙ₊₁ to
implement the cases of induction.


If Agda merely allowed datatype definitions at any expression, then none of this
module business would be necessary.
-}

data TypeCode₀ : Set where
⟦_⟧₀ : TypeCode₀ → Set
⟦_⟧₀ ()

module Universe {TypeCode : Set} {⟦_⟧ : TypeCode → Set} where
  mutual
    data TypeCodeₙ₊₁ : Set where
        `U : TypeCodeₙ₊₁
        `Π : (A : TypeCodeₙ₊₁) → (⟦_⟧ₙ₊₁ A → TypeCodeₙ₊₁) → TypeCodeₙ₊₁
        `lift : TypeCode → TypeCodeₙ₊₁

    ⟦_⟧ₙ₊₁ : TypeCodeₙ₊₁ → Set
    ⟦ `U ⟧ₙ₊₁ = TypeCode
    ⟦ `Π A B ⟧ₙ₊₁ = (a : ⟦ A ⟧ₙ₊₁) → ⟦ B a ⟧ₙ₊₁
    ⟦ `lift T ⟧ₙ₊₁ = ⟦ T ⟧

open Universe

mutual
  TypeCode : ℕ → Set
  TypeCode zero = TypeCode₀
  TypeCode (suc n) = TypeCodeₙ₊₁ {TypeCode n} {⟦_⟧}

  ⟦_⟧ : {n : ℕ} → TypeCode n → Set
  ⟦_⟧ {zero} T = ⟦ T ⟧₀
  ⟦_⟧ {suc n} T = ⟦ T ⟧ₙ₊₁

------------------------  "Shallow" embedding   --------------------------------
module Sᵀ where

  Ctx = Set
  Type : ℕ → Ctx → Set
  Type n Γ = Γ → TypeCode n
  Term : ∀{n} → (Γ : Ctx) → Type n Γ → Set
  Term Γ T = (γ : Γ) → ⟦ T γ ⟧
  Var : ∀{n} → (Γ : Ctx) → Type n Γ → Set
  Var Γ T = (γ : Γ) → ⟦ T γ ⟧
  nil : Ctx
  nil = ⊤
  cons : ∀{n} → (Γ : Ctx) → Type n Γ → Ctx
  cons Γ T = Σ Γ (λ γ → ⟦ T γ ⟧)

  U : ∀{n Γ} → Type (suc n) Γ
  U = λ _ → `U

  Π : ∀{n Γ} → (A : Type (suc n) Γ) → Type (suc n) (cons Γ A) → Type (suc n) Γ
  Π A B = λ γ → `Π (A γ) ((λ a → B (γ , a)))

  lambda : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
    → Term (cons Γ A) B → Term Γ (Π A B)
  lambda e = λ γ → λ a → e (γ , a)

  app : ∀{n Γ} → (A : Type (suc n) Γ) → (B : Type (suc n) (cons Γ A))
    → Term Γ (Π A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
  app A B e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

  weakenT : ∀{n m Γ} → (T : Type m Γ) → Type n Γ → Type n (cons Γ T)
  weakenT T A (γ , _) = A γ

  same : ∀{n Γ} → (T : Type n Γ) → Var {n} (cons Γ T) (weakenT T T)
  same T = λ (γ , t) → t
  next : ∀{n m Γ} → (A : Type n Γ) → (T : Type m Γ)
    → Var {n} Γ A → Var {n} (cons Γ T) (weakenT T A)
  next A T x = λ (γ , t) → x γ

  weaken : ∀{n Γ} → {T A : Type n Γ} → Term Γ T
    → Term (cons Γ A) (weakenT A T)
  weaken e = λ γ → e (proj₁ γ)

  Lift : ∀{n Γ} → (T : Type n Γ) → Type (suc n) Γ
  Lift T = λ γ → `lift (T γ)

  lift : ∀{n Γ} → (T : Type n Γ) → Term Γ T → Term Γ (Lift T)
  lift T e = e

  lower : ∀{n Γ} → (T : Type n Γ) → Term Γ (Lift T) → Term Γ T
  lower T e = e

  Sub : Ctx → Ctx → Set
  Sub Γ₂ Γ₁ = Γ₂ → Γ₁

  extend : ∀{n Γ₁ Γ₂} → (T : Type n Γ₁)
    → Sub Γ₂ Γ₁ → Term Γ₁ T → Sub Γ₂ (cons Γ₁ T)
  extend T sub e γ₂ = sub γ₂ , e (sub γ₂)

  idSub : ∀{Γ} → Sub Γ Γ
  idSub γ = γ

  weaken1Ren : ∀{Γ n T} → Sub (cons {n} Γ T) Γ
  weaken1Ren = proj₁

  subType : ∀{Γ₁ Γ₂ n} → Sub Γ₂ Γ₁ → Type n Γ₁ → Type n Γ₂
  subType sub T = λ γ₂ → T (sub γ₂)

  liftSub : ∀{Γ₁ Γ₂ n} → (sub : Sub Γ₂ Γ₁) → (T : Type n Γ₁)
    → Sub (cons Γ₂ (subType sub T)) (cons Γ₁ T)
  liftSub sub T (γ , t) = sub γ , t

  subTerm : ∀{Γ₁ Γ₂ n} → (T : Type n Γ₁) → (sub : Sub Γ₂ Γ₁)
    → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
  subTerm T sub e = λ γ₂ → e (sub γ₂)

-------------------- Augmented "shallow" embedding -----------------------------

data Context : Sᵀ.Ctx → Set₁ where
  ∅ : Context Sᵀ.nil
  _,_ : ∀{n SΓ} → (ctx : Context SΓ) → (T : Sᵀ.Type n SΓ) → Context (Sᵀ.cons SΓ T)

data Var : ∀{n} → {SΓ : Sᵀ.Ctx} → (Γ : Context SΓ) → (T : Sᵀ.Type n SΓ)
  → Sᵀ.Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Sᵀ.Type n SΓ} → {Γ : Context SΓ}
    → Var {n} (Γ , T) (Sᵀ.weakenT T T) (Sᵀ.same T)
  next : ∀{n m SΓ Γ A a} → {T : Sᵀ.Type n SΓ} → Var {m} {SΓ} Γ A a
    → Var (Γ , T) (Sᵀ.weakenT T A) (Sᵀ.next A T a)

data Term : ∀{n} → {SΓ : Sᵀ.Ctx} → (Γ : Context SΓ) → (T : Sᵀ.Type n SΓ)
  → Sᵀ.Term SΓ T → Set₁ where
  lambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Sᵀ.Type (suc n) SΓ}
    → {B : Sᵀ.Type (suc n) (Sᵀ.cons SΓ A)} → ∀{a}
    → Term (Γ , A) B a → Term Γ (Sᵀ.Π A B) (Sᵀ.lambda {n} {SΓ} {A} {B} a)
  var : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ}
    → {a : Sᵀ.Term SΓ T} → (icx : Var Γ T a) → Term {n} {SΓ} Γ T a
  app : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {A : Sᵀ.Type (suc n) SΓ}
      → {B : Sᵀ.Type (suc n) (Sᵀ.cons SΓ A)} → ∀{a₁ a₂}
      → Term {suc n} Γ (Sᵀ.Π A B) a₁ → (x : Term {suc n} Γ A a₂)
      → Term {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sᵀ.app A B a₁ a₂)
  Π : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {a₁ : Sᵀ.Term SΓ (Sᵀ.U {suc n})}
    → {a₂ : Sᵀ.Type (suc n) (Sᵀ.cons SΓ a₁)} → (A : Term Γ (Sᵀ.U {suc n}) a₁)
    → (B : Term (Γ , a₁) (Sᵀ.U {suc n}) a₂)
    → Term Γ (Sᵀ.U {suc n}) (Sᵀ.Π {n} a₁ a₂)
  U : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → Term {suc (suc n)} {SΓ} Γ Sᵀ.U Sᵀ.U
  Lift : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → ∀{a}
    → Term Γ (Sᵀ.U {n}) a → Term Γ (Sᵀ.U {suc n}) (Sᵀ.Lift a)
  lift : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ} → ∀{a}
    → Term Γ T a → Term Γ (Sᵀ.Lift T) (Sᵀ.lift T a)
  lower : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ} → ∀{a}
    → Term Γ (Sᵀ.Lift T) a → Term Γ T (Sᵀ.lift T a)

  -- Renamings and Substitutions on Term

Ren : ∀{sΓ₁ sΓ₂} → Sᵀ.Sub sΓ₂ sΓ₁ → Context sΓ₂ → Context sΓ₁ → Set₁
Ren sub Γ₂ Γ₁ = ∀{n T t} → Var {n} Γ₁ T t → Var Γ₂ (Sᵀ.subType sub T) (Sᵀ.subTerm T sub t)

idRen : ∀{sΓ Γ} → Ren {sΓ} Sᵀ.idSub Γ Γ
idRen x = x

liftRen : ∀{n sΓ₁ sΓ₂ T} → {sub : Sᵀ.Sub sΓ₂ sΓ₁} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₂ Γ₁ → Ren (Sᵀ.liftSub {_} {_} {n} sub T) (Γ₂ , Sᵀ.subType sub T) (Γ₁ , T)
liftRen ren same = same
liftRen ren (next x) = next (ren x)

weaken1Ren : ∀{sΓ Γ n T} → Ren {sΓ} (Sᵀ.weaken1Ren {sΓ} {n} {T}) (Γ , T) Γ
weaken1Ren = next

renTerm : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sᵀ.Sub sΓ₂ sΓ₁} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₂ Γ₁ → Term {n} Γ₁ T t → Term Γ₂ (Sᵀ.subType sub T) (Sᵀ.subTerm T sub t)
renTerm ren (lambda e) = lambda (renTerm (liftRen ren) e)
renTerm ren (var x) = var (ren x)
renTerm ren (app e₁ e₂) = app (renTerm ren e₁) (renTerm ren e₂)
renTerm ren (Π A B) = Π (renTerm ren A) (renTerm (liftRen ren) B)
renTerm ren U = U
renTerm ren (Lift e) = Lift (renTerm ren e)
renTerm ren (lift e) = lift (renTerm ren e)
renTerm ren (lower e) = lower (renTerm ren e)

Sub : ∀{sΓ₁ sΓ₂} → Sᵀ.Sub sΓ₂ sΓ₁ → Context sΓ₂ → Context sΓ₁ → Set₁
Sub sub Γ₂ Γ₁ = ∀{n T t} → Var {n} Γ₁ T t → Term Γ₂ (Sᵀ.subType sub T) (Sᵀ.subTerm T sub t)

idSub : ∀{sΓ Γ} → Sub {sΓ} Sᵀ.idSub Γ Γ
idSub x = var x

liftSub : ∀{n sΓ₁ sΓ₂ T} → {sub : Sᵀ.Sub sΓ₂ sΓ₁} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₂ Γ₁ → Sub (Sᵀ.liftSub {_} {_} {n} sub T) (Γ₂ , Sᵀ.subType sub T) (Γ₁ , T)
liftSub sub same = var same
liftSub sub (next x) = renTerm weaken1Ren (sub x)

subTerm : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sᵀ.Sub sΓ₂ sΓ₁} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₂ Γ₁ → Term {n} Γ₁ T t → Term Γ₂ (Sᵀ.subType sub T) (Sᵀ.subTerm T sub t)
subTerm sub (lambda e) = lambda (subTerm (liftSub sub) e)
subTerm sub (var x) = sub x
subTerm sub (app e₁ e₂) = app (subTerm sub e₁) (subTerm sub e₂)
subTerm sub (Π A B) = Π (subTerm sub A) (subTerm (liftSub sub) B)
subTerm sub U = U
subTerm sub (Lift e) = Lift (subTerm sub e)
subTerm sub (lift e) = lift (subTerm sub e)
subTerm sub (lower e) = lower (subTerm sub e)

extend : ∀{sΓ₁ sΓ₂ n Γ₁ Γ₂ sub} → {T : Sᵀ.Type n sΓ₁} → {t : Sᵀ.Term sΓ₁ T}
  → Sub {sΓ₁} {sΓ₂} sub Γ₂ Γ₁
  → Term Γ₁ T t → Sub (Sᵀ.extend T sub t) Γ₂ (Γ₁ , T)
extend sub e same = subTerm sub e
extend sub e (next x) = sub x

--------------------------------------------------------------------------------

Eq2 : {l : Level} {P : Set l} {Q : P → Set l}
  → (a₁ a₂ : P) → Q a₁ → Q a₂ → Set l
Eq2 {l} {P} {Q} a₁ a₂ b₁ b₂
  = _≡_ {l} {Σ P Q} (a₁ , b₁) (a₂ , b₂)

-- The propositional equality type, specialized to triples for convenience
Eq3 : {l : Level} {P : Set l} {Q : P → Set l} {R : (p : P) → Q p → Set l}
  → (a₁ a₂ : P) → (b₁ : Q a₁) → (b₂ : Q a₂) → R a₁ b₁ → R a₂ b₂ → Set l
Eq3 {l} {P} {Q} {R} a₁ a₂ b₁ b₂ c₁ c₂
  = _≡_ {l} {Σ P (λ a → Σ (Q a) (R a))} (a₁ , b₁ , c₁) (a₂ , b₂ , c₂)

castLamImpl : ∀{n SΓ Γ T t} → Term {suc n} {SΓ} Γ T t
  → Maybe (Σ (Sᵀ.Type (suc n) SΓ)
          (λ A → Σ (Sᵀ.Type (suc n) (Sᵀ.cons SΓ A))
          (λ B → Σ (Sᵀ.Term (Sᵀ.cons SΓ A) B)
          (λ t' → Σ (_≡_ {_} {(γ : SΓ) → Σ (TypeCode (suc n)) ⟦_⟧}
            (λ γ → (T γ , t γ))
            (λ γ → ((Sᵀ.Π A B) γ , λ a → t' (γ , a))))
          (λ p → Term (Γ , A) B t')))))
castLamImpl (lambda e) = just (_ , _ , _ , refl , e)
castLamImpl _ = nothing

Π-injective-typecode
  : ∀{n} → {A A' : TypeCode (suc n)} → {B : ⟦ A ⟧ → TypeCode (suc n)}
  → {B' : ⟦ A' ⟧ → TypeCode (suc n)}
  → {t : ⟦ `Π A B ⟧} → {t' : ⟦ `Π A' B' ⟧ }
  → (_≡_ {_} {Σ (TypeCode (suc n)) ⟦_⟧}
      ((`Π A B) , t)
      ((`Π A' B') , t'))
  → Eq3 A A' B B' t t'
Π-injective-typecode refl = refl

Π-injective : ∀{n Γ} → {A A' : Sᵀ.Type (suc n) Γ}
  → {B : Sᵀ.Type (suc n) (Sᵀ.cons Γ A)}
  → {B' : Sᵀ.Type (suc n) (Sᵀ.cons Γ A')}
  → {t : Sᵀ.Term (Sᵀ.cons Γ A) B}
  → {t' : Sᵀ.Term (Sᵀ.cons Γ A') B'}
  → _≡_ {_} {(γ : Γ) → Σ (TypeCode (suc n)) ⟦_⟧}
      (λ γ → ((Sᵀ.Π A B) γ , λ a → t (γ , a)))
      (λ γ → ((Sᵀ.Π A' B') γ , λ a → t' (γ , a)))
  → Eq3 A A' B B' t t'
Π-injective p
   = cong (λ f → (proj₁ ∘ f
                  , (λ (γ , a) → proj₁ (proj₂ (f γ)) a)
                  , λ (γ , a) → proj₂ (proj₂ (f γ)) a))
      (funExt (λ γ → Π-injective-typecode (happly p γ)))


castLam : ∀{n SΓ Γ A B t} → Term {suc n} {SΓ} Γ (Sᵀ.Π A B) t
  → Maybe (Term (Γ , A) B (λ (γ , a) → t γ a))
castLam {n} {SΓ} {Γ} e with castLamImpl e
... | nothing = nothing
... | just (A , B , t' , p , e') with (Π-injective p)
... | refl = just e'

βreduce : ∀{n sΓ Γ T t} → Term {n} {sΓ} Γ T t → Term {n} {sΓ} Γ T t
βreduce (lambda e) = lambda (βreduce e)
βreduce (var icx) = var icx
βreduce (Π A B) = Π (βreduce A) (βreduce B)
βreduce U = U
βreduce (lift e) = lift (βreduce e)
βreduce (lower e) = lower (βreduce e)
βreduce (Lift e) = Lift (βreduce e)
βreduce (app e₁ e₂) with castLam e₁
... | nothing = app (βreduce e₁) (βreduce e₂)
... | just e = subTerm (extend idSub e₂) e

-- (λ x . x) U
term1 : Term {2} ∅ Sᵀ.U Sᵀ.U
term1 = app (lambda (var same)) U

-- (λ x . x) U  =  U
test : βreduce term1 ≡ U
test = refl


--------------------------------------------------------------------------------
-- Some small things from the limitations section:
-- We mentioned that one can't prove that Π and U are unequal. This is because
-- If a context contains the empty type in it, then the type corresponding
-- to that context can's be instantiated

ΠcanEqualU : ∀{n A B} → Sᵀ.U {n} {⊥} ≡ Sᵀ.Π A B
ΠcanEqualU = funExt λ γ → ⊥-elim γ

-- On the other hand, in a context which is not equal to ⊥,
-- one CAN prove that Π ≠ U

Π≠UasTypecode : ∀{TC ev A B} → `U {TC} {ev} ≡ `Π A B → ⊥
Π≠UasTypecode ()

Π≠U : ∀{n Γ} → Γ → ∀{A B} → Sᵀ.U {n} {Γ} ≡ Sᵀ.Π A B → ⊥
Π≠U γ p = Π≠UasTypecode (cong (λ T → T γ) p)
