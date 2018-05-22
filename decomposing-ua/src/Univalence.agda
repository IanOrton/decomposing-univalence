{-# OPTIONS --without-K #-}

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import PropEqWithoutK
open import Prelude
open import IdRetract
open import Funext

-- Naive univalence
UA : (l : Level) → Set (lsuc l)
UA l = {A B : Set l} → Equiv A B → A ≡ B

--The computation rule for naive univalence
UAβ : ∀{l} → UA l → Set (lsuc l)
UAβ {l} ua = {A B : Set l}(e : Equiv A B) → coerce (ua e) ≡ proj₁ e

-- The proper univalence axiom (a la Voevodsky)
UAProper : (l : Level) → Set (lsuc l)
UAProper l = {A B : Set l} → isEquiv (Id→Equiv {A = A} {B})



-- Being an equivalence is a proposition, requires funext
isEquivProp : {l l' : Level}{A : Set l}{B : Set l'} → FunextNaive (l' ⊔ l) (l' ⊔ l) → (f : A → B)(e e' : isEquiv f) → e ≡ e'
isEquivProp {l} {l'} {A} {B} funext f e e' = lowerFunextNaive l l' funext (λ b → isContrProp (e b) (e' b)) where
  isContrProp : ∀{A}(x x' : isContr A) → x ≡ x'
  isContrProp (x , e) (x' , e') = Σext x≡x' (trans (subst-lemma (e' x) e) (funext λ a → subst-lemma' (e a) e')) where
    x≡x' : x ≡ x'
    x≡x' = sym (e' x)
    subst-lemma : ∀{x}(p : x' ≡ x)(e : (x' : _) → x ≡ x') → subst (λ a → (x : _) → a ≡ x) (sym p) e ≡ λ a → trans p (e a)
    subst-lemma refl e = refl
    subst-lemma' : ∀{a x y}(p : x ≡ y)(e : (x : _) → a ≡ x) → trans (e x) p ≡ e y
    subst-lemma' {x = x} refl e with e x
    ... | refl = refl


-- Naive univalence + β rule --> Proper univalence
UANaive→Proper : ∀{l} → FunextNaive l l → (Σ[ ua ∈ UA l ] UAβ ua) → UAProper l
UANaive→Proper funext (ua , uaβ) = IdRetract Equiv Id→Equiv ua uaβ' where
  uaβ' : ∀{A B}(p : Equiv A B) → Id→Equiv (ua p) ≡ p
  uaβ' p = Σext (uaβ p) (isEquivProp funext (proj₁ p) (subst isEquiv (uaβ p) (proj₂ (Id→Equiv (ua p)))) (proj₂ p))

-- Proper univalence --> Naive univalence + β rule
UAProper→Naive : ∀{l} → UAProper l → (Σ[ ua ∈ UA l ] UAβ ua)
UAProper→Naive ua-proper = (ua , uaβ) where
  ua : UA _
  ua e = proj₁ (proj₁ (ua-proper e))
  uaβ : UAβ ua
  uaβ e = cong proj₁ (proj₂ (proj₁ (ua-proper e)))

-- The equivalence induction principle
UAInduction : (l : Level) → Set (lsuc l)
UAInduction l =
  (A : Set l)
  (C : (B : Set l)(f : A → B)(e : isEquiv f) → Set l)
  (c₀ : C A id idEquiv)
  → ------------
  (B : Set l)(f : A → B)(e : isEquiv f) → C B f e

-- Proper univalence --> the equivalence induction principle
UAProper→Induction : ∀{l} → UAProper l → UAInduction l
UAProper→Induction ua-proper A C c₀ B f e = subst (λ{ (B , f , e) → C B f e }) eq c₀ where
  A=B : A ≡ B
  A=B = proj₁ (proj₁ (ua-proper (f , e)))
  eq : (A , id , idEquiv) ≡ (B , f , e)
  eq =
    trans
      (cong (λ{ (A , p) → (A , Id→Equiv p) }) (proj₂ (singContr A) (B , A=B)))
      (Σext refl (proj₂ (proj₁ (ua-proper (f , e)))))

-- The equivalence induction principle --> weak funext
-- This proof comes from the HoTT book.
UAInduction→FunextWeak : ∀{l} → UAInduction l → FunextWeak l l
UAInduction→FunextWeak {l} ua {A} {B} contr = retract-of-contr retr (equiv id) where
  isEquiv-postcomp : {A B C : Set l}(f : B → C) → isEquiv f → isEquiv {A = A → B} (f ∘_)
  isEquiv-postcomp {A} {B} {C} f e = ua B (λ C f e → isEquiv {A = A → B} (f ∘_)) idEquiv C f e
  α : (A → Σ[ x ∈ A ] B x) → (A → A)
  α = proj₁  ∘_
  α-inv : (A → A) → (A → Σ[ x ∈ A ] B x)
  α-inv f a = (f a , proj₁ (contr (f a)))
  retr : ((x : A) → B x) is-retract-of (fib α id)
  retr = (λ f → (λ a → a , f a) , refl) , (λ{ (f , eq) a → subst B (happly eq a) (proj₂ (f a)) }) , refl
  equiv : isEquiv α
  equiv = isEquiv-postcomp proj₁ equiv' where
    equiv' : isEquiv proj₁
    equiv' a = ((a , proj₁ (contr a)) , refl) , λ{ ((.a , b) , refl) → cong (λ b → ((a , b) , refl)) (proj₂ (contr a) b) }

UAProper→FunextNaive : ∀{l} → UAProper l → FunextNaive l l
UAProper→FunextNaive {l} ua = Weak→Naive l l (UAInduction→FunextWeak (UAProper→Induction ua))
