{-# OPTIONS --without-K #-}

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import PropEqWithoutK
open import Prelude
open import IdRetract
open import Funext
open import Univalence

----------------------------------------------------------------------
-- The principle that Σ is a point-wise congrunence.
--
-- ΣCong l follows from Funext l (lsuc l), but can be stated in terms
-- of a single universe level l. Further, ΣCong l follows from UA l,
-- whereas deriving Funext l (lsuc l) from UA would require UA (lsuc l)
----------------------------------------------------------------------
ΣCong : (l : Level) → Set (lsuc l)
ΣCong l = {A : Set l}{B B' : A → Set l} → B ~ B' → Σ A B ≡ Σ A B'

ΣCongβ : ∀{l} → ΣCong l → Set (lsuc l)
ΣCongβ {l} Σcong = {A : Set l}{B B' : A → Set l} → (p : B ~ B') → coerce (Σcong p) ≡ λ{ (a , b) → (a , coerce (p a) b) }

UA→ΣCong : ∀{l} → UA l → ΣCong l
UA→ΣCong ua {A = A} {B} {B'} h = Σ= where
  f : Σ A B → Σ A B'
  f (a , b) = a , coerce (h a) b
  g : Σ A B' → Σ A B
  g (a , b') = a , coerce (sym (h a)) b'
  fg~id : (f ∘ g) ~ id
  fg~id (a , b') = Σext refl (coerce-sym (h a) b') where
    coerce-sym : ∀{A B}(p : A ≡ B)(y : B) → coerce p (coerce (sym p) y) ≡ y
    coerce-sym refl _ = refl
  gf~id : (g ∘ f) ~ id
  gf~id (a , b) = Σext refl (coerce-sym (h a) b) where
    coerce-sym : ∀{A B}(p : A ≡ B)(x : A) → coerce (sym p) (coerce p x) ≡ x
    coerce-sym refl _ = refl
  Σ= : Σ A B ≡ Σ A B'
  Σ= = ua (f , isHAE→isEquiv f (Qinv→isHAE f (g , gf~id , fg~id)))

UAβ→ΣCongβ : ∀{l}(ua : UA l) → UAβ ua → {A : Set l}{B B' : A → Set l}(h : B ~ B') → coerce (UA→ΣCong ua h) ≡ λ{ (a , b) → (a , coerce (h a) b) }
UAβ→ΣCongβ ua uaβ {A = A} {B} {B'} h = uaβ _

----------------------------------------------------------------------
-- Axioms for producing paths
----------------------------------------------------------------------
-- The three axioms
UnitRight : (l : Level) → Set (lsuc l)
UnitRight l = (A : Set l) → A ≡ (A × ⊤ {l})

Flip : (l₀ l₁ l₂ : Level) → Set (lsuc (l₂ ⊔ (l₁ ⊔ l₀)))
Flip l₀ l₁ l₂ = {A : Set l₀}{B : Set l₁}{C : A → B → Set l₂} → (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) ≡ (Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)

Contract : (l : Level) → Set (lsuc l)
Contract l = {A : Set l} → isContr A → A ≡ ⊤

-- All three axioms follow from UA
A≅ΣA⊤ : ∀{l}{A : Set l} → Equiv A (A × ⊤ {l})
A≅ΣA⊤ {A = A} = (f , e) where
  f : A → Σ[ _ ∈ A ] ⊤
  f a = (a , tt)
  e : isEquiv f
  e (a , tt) = (a , refl) , (λ{ (.a , refl) → refl })
ua-implies-ur : ∀{l} → UA l → UnitRight l
ua-implies-ur ua A = ua A≅ΣA⊤

ΣABC≅ΣBAC : ∀{l₀ l₁ l₂}{A : Set l₀}{B : Set l₁}{C : A → B → Set l₂}
  → Equiv (Σ[ a ∈ A ] Σ[ b ∈ B ] C a b) (Σ[ b ∈ B ] Σ[ a ∈ A ] C a b)
ΣABC≅ΣBAC {A = A} {B} {C} = (f , e) where
  f : Σ[ a ∈ A ] Σ[ b ∈ B ] C a b → Σ[ b ∈ B ] Σ[ a ∈ A ] C a b
  f (a , b , c) = (b , a , c)
  e : isEquiv f
  e (b , a , c) = ((a , b , c) , refl) , (λ{ (_ , refl) → refl })
ua-implies-flip : ∀{l₀ l₁ l₂} → UA (l₂ ⊔ (l₁ ⊔ l₀)) → Flip l₀ l₁ l₂
ua-implies-flip ua {A} {B} {C} = ua ΣABC≅ΣBAC

ua-implies-contract : ∀{l} → UA l → Contract l
ua-implies-contract ua {A = A} (a , all-eq) = ua (f , e) where
  f : A → ⊤
  f a = tt
  ⊤-isSet : {x : ⊤}{p : x ≡ x} → p ≡ refl
  ⊤-isSet {p = refl} = refl
  e : isEquiv f
  e tt = (a , refl) , (λ{ (a' , refl) → Σext (all-eq a') (⊤-isSet)})

----------------------------------------------------------------------
-- UA follows from the axioms (and Σcong)
----------------------------------------------------------------------
open ≡-Reasoning

ua-from-axioms :
  ∀{l}
  → ΣCong l
  → UnitRight l
  → Flip l l l
  → Contract l
  → --------------
  UA l
ua-from-axioms {l} Σcong unit-r flip contract {A} {B} (f , e) =
    A
  ≡⟨ unit-r A ⟩
    Σ A (λ _ → ⊤)
  ≡⟨ Σcong (λ a → sym (contract (singContr (f a)))) ⟩
    (Σ[ a ∈ A ] Σ[ b ∈ B ] f a ≡ b)
  ≡⟨ flip ⟩
    (Σ[ b ∈ B ] Σ[ a ∈ A ] f a ≡ b)
  ≡⟨ Σcong (λ b → contract (e b)) ⟩
    Σ B (λ _ → ⊤)
  ≡⟨ sym (unit-r B) ⟩
    B
  ∎

----------------------------------------------------------------------
-- Axioms for transporting along paths
----------------------------------------------------------------------

-- The assumptions we make
UnitRightβ : ∀{l} → UnitRight l → Set (lsuc l)
UnitRightβ {l} unit-r = (A : Set l) → coerce (unit-r A) ≡ λ a → (a , tt)

Flipβ : ∀{l₀ l₁ l₂} → Flip l₀ l₁ l₂ → Set (lsuc (l₂ ⊔ (l₁ ⊔ l₀)))
Flipβ {l₀} {l₁} {l₂} flip = ∀{A B C} → coerce (flip {A} {B} {C}) ≡ (λ{(a , b , c) → (b , a , c)})

-- These properties follow from UAβ, for the terms constructed earlier from ua
uaβ-implies-urβ : ∀{l}(ua : UA l) → UAβ ua → UnitRightβ (ua-implies-ur ua)
uaβ-implies-urβ ua uaβ A = uaβ A≅ΣA⊤

uaβ-implies-fβ : ∀{l₀ l₁ l₂}(ua : UA (l₂ ⊔ (l₁ ⊔ l₀))) → UAβ ua → Flipβ {l₀} {l₁} {l₂} (ua-implies-flip ua)
uaβ-implies-fβ ua uaβ = uaβ ΣABC≅ΣBAC


----------------------------------------------------------------------
-- Proof that UAβ follows from these properties
----------------------------------------------------------------------
uaβ-from-axioms :
  ∀{l}
  -- Extensionality principles
  → (funext : FunextNaive l l)
  → (Σcong  : ΣCong l) 
  → (Σcongβ : ΣCongβ Σcong) 
  -- The equalities
  → (unir : UnitRight l)
  → (flip : Flip l l l)
  → (cont : Contract l)
  -- Their computation rules
  → UnitRightβ unir
  → Flipβ flip
  -------------------
  → UAβ (ua-from-axioms Σcong unir flip cont)
uaβ-from-axioms {l} funext Σcong Σcongβ unit-r flip contract urβ flipβ {A} {B} e = split-subst
    {p = unit-r A}{Σcong (λ a → sym (contract (singContr (proj₁ e a))))}
    {flip}{Σcong (λ b → contract (proj₂ e b))}{sym (unit-r B)}
    (urβ A) (Σcongβ' (λ a → sym (contract (singContr (proj₁ e a)))) (λ a → csβ (singContr (proj₁ e a))))
    flipβ (Σcongβ' (λ b → contract (proj₂ e b)) (λ _ → refl)) (ursβ B)
      
      where

        split-subst :
          {A B C D E F : Set l}
          {p : A ≡ B}{q : B ≡ C}{r : C ≡ D}{s : D ≡ E}{t : E ≡ F}
          {f : A → B}{g : B → C}{h : C → D}{i : D → E}{j : E → F}
          (p-eq : coerce p ≡ f)(q-eq : coerce q ≡ g)
          (r-eq : coerce r ≡ h)(s-eq : coerce s ≡ i)
          (t-eq : coerce t ≡ j)
          →
          coerce (trans p (trans q (trans r (trans s (trans t refl))))) ≡ (λ x → (j (i (h (g (f x))))))
        split-subst {p = refl} {refl} {refl} {refl} {refl} refl refl refl refl refl = refl

        ursβ : (A : Set l) → coerce (sym (unit-r A)) ≡ proj₁
        ursβ A = coe-sym (unit-r A) proj₁ (cong (λ f → (λ x → proj₁ (f x))) (urβ A)) where
          coe-sym : {A B : Set l}(p : A ≡ B)(g : B → A)(inv : (λ x → g (coerce p x)) ≡ (λ x → x)) → coerce (sym p) ≡ g
          coe-sym refl g inv = sym inv

        csβ : {A : Set l}(c : isContr A) → coerce (sym (contract c)) ≡ (λ _ → proj₁ c)
        csβ (a , all-eq) = funext (λ u → sym (all-eq (coerce (sym (contract (a , all-eq))) u)))

        -- A modified version of Σcongβ
        Σcongβ' : {A : Set l}{B B' : A → Set l}(p : (x : A) → B x ≡ B' x)
          {f : (a : A) → B a → B' a}
          → ((a : A) → coerce (p a) ≡ f a)
          → coerce (Σcong {A} {B} {B'} p) ≡ (λ{ (a , b) → (a , f a b)})
        Σcongβ' {A} p {f} subst-eq =
          begin
            coerce (Σcong p)
          ≡⟨ Σcongβ p ⟩
            (λ{ (a , b) → (a , coerce (p a) b) })
          ≡⟨ funext ((λ{ (a , b) → Σext refl (happly (subst-eq a) b)})) ⟩
            (λ{ (a , b) → (a , f a b)})
          ∎

----------------------------------------------------------------------
-- To sum up
----------------------------------------------------------------------
record AllAxioms (l : Level) : Set (lsuc l) where
  constructor ax
  field
    -- The equalities
    unir : UnitRight l
    flip : Flip l l l
    cont : Contract l
    -- Their computation rules
    unirβ : UnitRightβ unir
    flipβ : Flipβ flip

UAEquiv :
  ∀{l}
  (funext  : FunextNaive l l)
  (Σcong  : ΣCong l)
  (Σcongβ : ΣCongβ Σcong)
  → ----------------------
  (Σ[ ua ∈ UA l ] UAβ ua) ⟷ AllAxioms l
UAEquiv {l} funext Σcong Σcongβ = forwards , backwards where
  forwards : (Σ[ ua ∈ UA l ] UAβ ua) → AllAxioms l
  forwards (ua , uaβ) =
    ax (ua-implies-ur ua) (ua-implies-flip ua) (ua-implies-contract ua)
      (uaβ-implies-urβ ua uaβ) (uaβ-implies-fβ ua uaβ)
  backwards : AllAxioms l → (Σ[ ua ∈ UA l ] UAβ ua)
  backwards (ax unir flip cont unirβ flipβ) =
    (ua-from-axioms Σcong unir flip cont) , (uaβ-from-axioms funext Σcong Σcongβ unir flip cont unirβ flipβ)

UAEquivProper :
  ∀{l}
  → ----------------------
  UAProper l ⟷ (
    FunextNaive l l ×
    (Σ (ΣCong l) ΣCongβ) ×
    AllAxioms l
  )
UAEquivProper {l} = forwards , backwards where
  forwards : UAProper l → (FunextNaive l l × (Σ[ Σcong ∈ (ΣCong l) ] ΣCongβ Σcong) × AllAxioms l)
  forwards ua-proper = (funext , (Σcong , Σcongβ) , proj₁ (UAEquiv funext Σcong Σcongβ) (UAProper→Naive ua-proper)) where
    funext : FunextNaive l l
    funext = UAProper→FunextNaive ua-proper
    Σcong : ΣCong l
    Σcong = UA→ΣCong (proj₁ (UAProper→Naive ua-proper))
    Σcongβ : ΣCongβ Σcong
    Σcongβ = UAβ→ΣCongβ (proj₁ (UAProper→Naive ua-proper)) (proj₂ (UAProper→Naive ua-proper))
  backwards : (FunextNaive l l × (Σ[ Σcong ∈ (ΣCong l) ] ΣCongβ Σcong) × AllAxioms l) → UAProper l
  backwards (funext , (Σcong , Σcongβ) , axioms) = UANaive→Proper funext (proj₂ (UAEquiv funext Σcong Σcongβ) axioms)

-- If we assume funext at all levels (as in the paper) then all the
-- extensionality assumptions disappear from the previous theorems
postulate
  funext' : ∀{l l'} → FunextNaive l l'

funext-proper : ∀{l l'} → FunextProper l l'
funext-proper {l} {l'} = Naive→Proper l l' funext'

funext : ∀{l l'} → FunextNaive l l'
funext H = proj₁ (proj₁ (funext-proper H))

Σcong : ∀{l} → ΣCong l
Σcong {A = A} H = cong (Σ A) (funext H)

Σcongβ : ∀{l} → ΣCongβ (Σcong {l})
Σcongβ {l} {A} {B} {B'} H = trans (coerceΣ (funext H)) (cong (λ H → (λ { (a , b) → a , coerce (H a) b })) (proj₂ (proj₁ (funext-proper H)))) where
  coerceΣ : (p : B ≡ B') → coerce (cong (Σ A) p) ≡ λ{ (a , b) → (a , coerce (happly p a) b) }
  coerceΣ refl = refl

UAEquiv' : ∀{l} → (Σ[ ua ∈ UA l ] UAβ ua) ⟷ AllAxioms l
UAEquiv' = UAEquiv funext Σcong Σcongβ

UAEquivProper' : ∀{l} → UAProper l ⟷ AllAxioms l
UAEquivProper' = (proj₂ ∘ proj₂) ∘ (proj₁ UAEquivProper) , (λ ax → proj₂ UAEquivProper (funext , (Σcong , Σcongβ) , ax))
