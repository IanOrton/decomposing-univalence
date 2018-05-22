{-# OPTIONS --without-K #-}

open import Agda.Primitive using (Level; _⊔_ ;lsuc)
open import PropEqWithoutK
open import Prelude
open import IdRetract

----------------------------------------------------------------------
-- Function extensionality
----------------------------------------------------------------------
-- The canonical proof that f ~ f
~refl : {l l' : Level}{A : Set l}{B : A → Set l'}{f : (x : A) → B x} → f ~ f
~refl _ = refl

-- The canonical map (f ≡ g) → (f ~ g)
happly : {l l' : Level}{A : Set l}{B : A → Set l'}{f g : (x : A) → B x} → f ≡ g → f ~ g
happly refl = ~refl

-- The proper function extensionality axiom
FunextProper : (l l' : Level) → Set (lsuc (l' ⊔ l))
FunextProper l l' = {A : Set l}{B : A → Set l'}{f g : (x : A) → B x} → isEquiv (happly {l} {l'} {A} {B} {f} {g})

-- The naive function extensionality axiom
FunextNaive : (l l' : Level) → Set (lsuc (l' ⊔ l))
FunextNaive l l' = {A : Set l}{B : A → Set l'}{f g : (x : A) → B x} → f ~ g → f ≡ g


-- We now show that FunextNaive is equivalent to FunextProper. This result is
-- due to Voevodsky, but the details of the proof given here come from a blog
-- post by Peter LeFanu Lumsdaine:
--
--   https://homotopytypetheory.org/2011/12/19/strong-funext-from-weak/
--
_is-retract-of_ : ∀{l l'} → Set l → Set l' → Set (l' ⊔ l)
A is-retract-of B = Σ[ i ∈ (A → B) ] Σ[ r ∈ (B → A) ] (r ∘ i ≡ id)

lemma1 :
  ∀{l l'}
  (ext : FunextNaive l l')
  {A : Set l}{B : A → Set l'}
  (f : (x : A) → B x)
  → --------------------
  (Σ[ g ∈ ((x : A) → B x) ] (f ~ g)) is-retract-of ((x : A) → Σ[ y ∈ B x ] f x ≡ y)
lemma1 ext {A} {B} f = forwards , backwards , refl where
  forwards : (Σ[ g ∈ ((x : A) → B x) ] (f ~ g)) → ((x : A) → Σ[ y ∈ B x ] f x ≡ y)
  forwards (g , h) x = g x , h x
  backwards : ((x : A) → Σ[ y ∈ B x ] f x ≡ y) → (Σ[ g ∈ ((x : A) → B x) ] (f ~ g))
  backwards k = (λ x → proj₁ (k x)) , (λ x → proj₂ (k x))

lemma2 :
  ∀{l l'}
  (ext : FunextNaive l l')
  {A : Set l}{B : A → Set l'}
  (f : (x : A) → B x)
  → --------------------
  isContr ((x : A) → Σ[ y ∈ B x ] f x ≡ y)
lemma2 ext {A} {B} f = ctr , eq where
  ctr : (x : A) → Σ[ y ∈ B x ] f x ≡ y
  ctr x = (f x , refl)
  eq : (k : (x : A) → Σ[ y ∈ B x ] f x ≡ y) → ctr ≡ k
  eq k = ext (λ x → proj₂ (singContr (f x)) (k x))

retract-of-contr :
  ∀{l l'}
  {A : Set l}
  {B : Set l'}
  → A is-retract-of B
  → isContr B
  → isContr A
retract-of-contr (i , r , p) (b₀ , eq) = (r b₀) , (λ a → trans (cong r (eq (i a))) (happly p a))

lemma3 :
  ∀{l l'}
  (ext : FunextNaive l l')
  {A : Set l}{B : A → Set l'}
  (f : (x : A) → B x)
  → --------------------
  isContr (Σ[ g ∈ ((x : A) → B x) ] (f ~ g))
lemma3 ext f = retract-of-contr (lemma1 ext f) (lemma2 ext f)

-- We may need to modify a naive funext to get the right computation rule
fix :
  ∀{l l'}
  (ext : FunextNaive l l')
  → --------------------
  FunextNaive l l'
fix ext h = trans (ext h) (sym (ext ~refl))

-- Naive funext implies proper funext
Naive→Proper : (l l' : Level) → FunextNaive l l' → FunextProper l l'
Naive→Proper l l' ext {A} {B} = IdRetract _~_ happly ext' happly∘ext where
  ext' : ∀{f g} → f ~ g → f ≡ g
  ext' = fix ext
  ext'~refl : ∀{f} → ext' {f} ~refl ≡ refl
  ext'~refl = trans-sym (ext ~refl) where 
    trans-sym : {x y : _}(p : x ≡ y) → trans p (sym p) ≡ refl
    trans-sym refl = refl
  happly∘ext : ∀{f g}(h : f ~ g) → happly (ext' h) ≡ h
  happly∘ext {f} {g} h = subst C path c₀ where
    C : (Σ[ g ∈ ((x : A) → B x) ] (f ~ g)) → Set _
    C (g , h) = happly (ext' h) ≡ h
    path : (f , ~refl) ≡ (g , h)
    path = proj₂ (lemma3 ext f) (g , h)
    c₀ : happly (ext' ~refl) ≡ ~refl
    c₀ = cong happly ext'~refl

-- Theorem 3.1. The two axioms are equivalent.
FunextEquiv : (l l' : Level) → FunextProper l l' ⟷ FunextNaive l l'
FunextEquiv l l' = forwards , (Naive→Proper l l') where
  forwards : FunextProper l l' → FunextNaive l l'
  forwards funext f~g = proj₁ (proj₁ (funext f~g))

lowerFunextNaive : ∀{l₀ l₁} l₀' l₁' → FunextNaive (l₀ ⊔ l₀') (l₁ ⊔ l₁') → FunextNaive l₀ l₁
lowerFunextNaive l₀' l₁' funext p =
  cong (λ h → lower ∘ h ∘ lift)
    (funext (λ x → cong (lift {ℓ = l₁'}) (p (lower {ℓ = l₀'} x))))


-- Details of this proof come from a blog by Paolo Capriotti:
-- https://www.paolocapriotti.com/blog/2013/09/18/another-proof-of-funext/index.html 

FunextWeak : (l l' : Level) → Set (lsuc (l' ⊔ l))
FunextWeak l l' =
  {A : Set l}{B : A → Set l'}
  → ((x : A) → isContr (B x))
  → isContr ((x : A) → B x)

Weak→Naive : (l l' : Level) → FunextWeak l l' → FunextNaive l l'
Weak→Naive l l' wext {f = f} {g} h = cong (λ f x → proj₁ (f x)) p' where
  f' : (x : _) → Σ[ y ∈ _ ] f x ≡ y
  f' x = f x , refl
  g' : (x : _) → Σ[ y ∈ _ ] f x ≡ y
  g' x = g x , h x
  p' : f' ≡ g'
  p' = trans (sym (proj₂ (wext (λ x → singContr (f x))) f'))
    (proj₂ (wext (λ x → singContr (f x))) g')
