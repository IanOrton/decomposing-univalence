{-# OPTIONS --without-K #-}

open import PropEqWithoutK
open import Agda.Primitive using (Level; _⊔_)

----------------------------------------------------------------------
-- Lifting (from the agda standard library).
----------------------------------------------------------------------
record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

----------------------------------------------------------------------
-- Function composition and the id function
----------------------------------------------------------------------
infixr 9 _∘_
_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

id : {l : Level}{A : Set l} → A → A
id x = x

----------------------------------------------------------------------
-- The Unit type (from the agda standard library).
----------------------------------------------------------------------
record ⊤ {l : Level} : Set l where
  instance constructor tt

----------------------------------------------------------------------
-- Dependent products (from the agda standard library).
----------------------------------------------------------------------
infixr 4 _,_
infixr 2 _×_ 

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

-- Extensionality for sums
Σext :
  {a b : Level}
  {A : Set a}
  {B : A → Set b}
  {a a' : A}
  {b : B a}
  {b' : B a'}
  (p : a ≡ a')
  (q : subst B p b ≡ b')
  → ---------------------
  (a , b) ≡ (a' , b')
Σext refl refl = refl

----------------------------------------------------------------------
-- Standard definitions
----------------------------------------------------------------------
-- Logical equivalence
_⟷_ : {l l' : Level} → Set l → Set l' → Set (l' ⊔ l)
A ⟷ B = (A → B) × (B → A)

-- Contractibility
isContr : {l : Level} → Set l → Set l
isContr A = Σ[ a₀ ∈ A ] ((x : A) → a₀ ≡ x)

-- Singletons
Sing : ∀{l}{A : Set l} → A → Set l
Sing {A = A} a₀ = Σ[ a ∈ A ] a₀ ≡ a

-- Singletons are contractible
singContr : ∀{l}{A : Set l}(a₀ : A) → isContr (Sing a₀)
proj₁ (singContr a₀) = (a₀ , refl)
proj₂ (singContr a₀) (.a₀ , refl) = refl

-- Homotopies between functions
_~_ : {l l' : Level}{A : Set l}{B : A → Set l'}(f g : (x : A) → B x) → Set (l' ⊔ l)
f ~ g = (x : _) → f x ≡ g x

----------------------------------------------------------------------
-- Quasi inverses
----------------------------------------------------------------------
Qinv : {l l' : Level}{A : Set l}{B : Set l'}(f : A → B) → Set (l' ⊔ l)
Qinv {A = A} {B} f = Σ[ g ∈ (B → A) ] (((g ∘ f) ~ id) × ((f ∘ g) ~ id))

----------------------------------------------------------------------
-- Different notions of equivalence
----------------------------------------------------------------------
-- Half adjoint equivs
isHAE : {l l' : Level}{A : Set l}{B : Set l'}(f : A → B) → Set (l' ⊔ l)
isHAE {A = A} {B} f =
  Σ[ g ∈ (B → A) ]
  Σ[ η ∈ (g ∘ f) ~ id ]
  Σ[ ε ∈ (f ∘ g) ~ id ]
  ((x : A) → cong f (η x) ≡ ε (f x))

-- Qinv implies isHAE
Qinv→isHAE : {l l' : Level}{A : Set l}{B : Set l'}(f : A → B) → Qinv f → isHAE f
Qinv→isHAE f (g , η , ε) = (g , η , ε' , τ) where
  ε' : (f ∘ g) ~ id
  ε' b = trans (sym (ε (f (g b)))) (trans (cong f (η (g b))) (ε b))
  τ : (x : _) → cong f (η x) ≡ ε' (f x)
  τ a = eq₂ where
    trans-sym : {x y z : _}(p : x ≡ y)(q : y ≡ z) → trans (sym p) (trans p q) ≡ q
    trans-sym refl _ = refl
    trans-refl : ∀{l}{A : Set l}{x y : A}(p : x ≡ y) → trans p refl ≡ p
    trans-refl refl = refl
    trans-inj : ∀{x y z}(p p' : x ≡ y)(q : y ≡ z) → trans p q ≡ trans p' q → p ≡ p'
    trans-inj p p' refl r = trans (trans (sym (trans-refl p)) r) (trans-refl p')
    cong-id : ∀{x y}(p : x ≡ y) → cong id p ≡ p
    cong-id refl = refl
    cong-cong : ∀{l l' l''}{A : Set l}{B : Set l'}{C : Set l''}{f : A → B}{g : B → C}{x y : A}(p : x ≡ y) → cong g (cong f p) ≡ cong (g ∘ f) p
    cong-cong refl = refl
    htpy-nat : ∀{l l'}{A : Set l}{B : Set l'}{x y : A}{f g : A → B}(H : f ~ g)(p : x ≡ y) → trans (H x) (cong g p) ≡ trans (cong f p) (H y)
    htpy-nat H refl = trans-refl (H _)
    eq₀ : η (g (f a)) ≡ cong (g ∘ f) (η a)
    eq₀ = trans-inj (η (g (f a)))
      (cong (λ z → g (f z)) (η a)) (η a) 
      (trans (cong (trans (η (g (f a)))) (sym (cong-id (η a))))
        (htpy-nat η (η a)))
    eq₁ : trans (cong f (η (g (f a)))) (ε (f a)) ≡ trans (ε (f (g (f a)))) (cong f (η a))
    eq₁ =
      trans
        (cong (λ p → trans (cong f p) (ε (f a))) eq₀)
        (trans
          (cong (λ p → trans p (ε (f a))) (cong-cong (η a)))
          (sym (htpy-nat (λ x → ε (f x)) (η a)))
        )
    eq₂ : cong f (η a) ≡ trans (sym (ε (f (g (f a))))) (trans (cong f (η (g (f a)))) (ε (f a)))
    eq₂ =
      sym (trans
        (cong (trans (sym (ε (f (g (f a)))))) eq₁)
        (trans-sym (ε (f (g (f a)))) (cong f (η a)))
      )

-- The fibers of a function
fib : {l l' : Level}{A : Set l}{B : Set l'}(f : A → B)(b : B) → Set (l' ⊔ l)
fib {A = A} f b = Σ[ a ∈ A ] f a ≡ b

-- Equivalences in terms of contractible fibers
isEquiv : {l l' : Level}{A : Set l}{B : Set l'}(f : A → B) → Set (l' ⊔ l)
isEquiv {A = A} {B} f = (b : B) → isContr (fib f b)

-- isHAE implies isEquiv
isHAE→isEquiv : {l l' : Level}{A : Set l}{B : Set l'}(f : A → B) → isHAE f → isEquiv f
isHAE→isEquiv f (g , η , ε , τ) b = (g b , ε b) , contr where
  contr : (x : fib f b) → (g b , ε b) ≡ x
  contr (a , refl) = subst-lemma (η a) (trans (trans-refl (cong f (η a))) (τ a)) where
    subst-lemma : ∀{x y }{u}{p : f x ≡ u}{q : f y ≡ u}(r : x ≡ y) → trans (cong f r) q ≡ p → (x , p) ≡ (y , q)
    subst-lemma refl refl = refl
    trans-refl : ∀{x y}(p : x ≡ y) → trans p refl ≡ p
    trans-refl refl = refl

-- isEquiv implies Qinv
isEquiv→Qinv : {l l' : Level}{A : Set l}{B : Set l'}(f : A → B) → isEquiv f → Qinv f
isEquiv→Qinv {A = A} {B} f equiv = g , gf~id , fg~id where
  g : B → A
  g b = proj₁ (proj₁ (equiv b))
  gf~id : (x : A) → g (f x) ≡ x
  gf~id x = cong proj₁ (proj₂ (equiv (f x)) (x , refl))
  fg~id : (x : B) → f (g x) ≡ x
  fg~id x = proj₂ (proj₁ (equiv x))

-- We will use the contractible fibers definition
Equiv : ∀{l l'} → Set l → Set l' → Set (l' ⊔ l)
Equiv A B = Σ[ f ∈ (A → B) ] isEquiv f

idEquiv : ∀{l}{A : Set l} → isEquiv {A = A} id
idEquiv = λ a → (a , refl) , λ{ (x , refl) → refl }

-- Id→Equiv
Id→Equiv : ∀{l}{A B : Set l} → A ≡ B → Equiv A B
Id→Equiv refl = id , idEquiv

-- Coercion is defined Id→Equiv
coerce : ∀{l}{A B : Set l} → A ≡ B → A → B
coerce p = proj₁ (Id→Equiv p)

