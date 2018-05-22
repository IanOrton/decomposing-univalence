{-# OPTIONS --rewriting #-}
module realignment where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations

realign :
  {Γ : Set}
  {Φ : Γ → Cof}
  {A : Γ → Set}
  (β : isFib {Γ = res Γ Φ} (A ∘ fst))
  (α : isFib A)
  → ---------------
  isFib A
abstract
  realign {Γ} {Φ} {A} β α e p ψ f (a , ext) = (fst a') , (λ u → snd a' ∣ inl u ∣) where

    -- If the p stays entirely in Γ,Φ then we can fill using β
    aFill : (∀iΦ : [ ∀i (Φ ∘ p) ]) → ⟦ a' ∈ ((i : Int) → A (p i)) ∣ ((ψ , f) ↗ a') & (a' ⟨ e ⟩ ≈ a) ⟧
    aFill ∀iΦ = fill {A = A ∘ fst} e β (λ i → (p i) , ∀iΦ i) ψ f a ext

    -- Now we define f' to be f when ψ holds and aFill when ∀i (Φ ∘ p) holds
    f' : [ ψ ∨ ∀i (Φ ∘ p) ] → Π (A ∘ p)
    f' = _∪_ {φ = ψ} {ψ = ∀i (Φ ∘ p)} f (λ u → fst (aFill u)) {λ v ∀Φi → fst (snd (aFill ∀Φi)) v}

    -- Show that f' extends to a at e
    ext' : prf ((ψ ∨ ∀i (Φ ∘ p) , f') ∙ ⟨ e ⟩ ↗ a)
    ext' = or-elim-eq (λ u → f' u ⟨ e ⟩) a (λ {l} → ext l) (λ {r} → snd (snd (aFill r)))

    -- The main construction:
    a' : ⟦ a ∈ A (p ⟨ ! e ⟩) ∣ (ψ ∨ ∀i (Φ ∘ p) , f') ∙ ⟨ ! e ⟩ ↗ a ⟧
    a' = α e p (ψ ∨ ∀i (Φ ∘ p)) f' (a , ext')


isFixed : 
  {Γ : Set}
  {Φ : Γ → Cof}
  {A : Γ → Set}
  (β : isFib {Γ = res Γ Φ} (A ∘ fst))
  (α : isFib A)
  → ---------------
  reindex A (realign {Φ = Φ} {A} β α) fst ≡ β
abstract
  isFixed {Γ} {Φ} {A} β α = fibExt {A = A ∘ fst} calc where
    calc : (e : OI) (p : Int → Σ Γ (λ x → [ Φ x ])) (φ : Cof)
        (f : [ φ ] → Π (A ∘ fst ∘ p))
        (a₀ : set (A (fst (p ⟨ e ⟩))) (_↗_ ((φ , f) ∙ ⟨ e ⟩))) →
        fst (reindex A (realign {Γ} {Φ} {A} β α) fst e p φ f a₀) ≡ fst (β e p φ f a₀)
    calc e p ψ f (g , ext) =
      proof:
        fst (realign {Γ} {Φ} {A} β α e p' ψ f (g , ext))
      ≡[ refl ]≡
        fst (α e p' (ψ ∨ ∀i (Φ ∘ p')) f' (g , ext'))
      ≡[ symm (snd (α e p' (ψ ∨ ∀i (Φ ∘ p')) f' (g , ext')) ∣ inr (λ i → snd (p i)) ∣) ]≡
        fst (aFill (λ i → snd (p i))) ⟨ ! e ⟩
      ≡[ fillAtEnd e β p ψ f g ext ]≡
        fst (β e p ψ f (g , ext))
      qed where
        p' : Int → Γ
        p' i = fst (p i)
        aFill : (∀iΦ : [ ∀i (Φ ∘ p') ]) →
          ⟦ a' ∈ ((i : Int) → A (p' i)) ∣
            ((ψ , f) ↗ a') & (a' ⟨ e ⟩ ≈ g) ⟧
        aFill ∀iΦ = fill {A = A ∘ fst} e β (λ i → (p' i) , ∀iΦ i) ψ f g ext
        f' : [ ψ ∨ ∀i (Φ ∘ p') ] → Π (A ∘ p')
        f' = _∪_ {φ = ψ} {ψ = ∀i (Φ ∘ p')} f (λ u → fst (aFill u)) {λ v ∀Φi → fst (snd (aFill ∀Φi)) v}
        ext' : prf ((ψ ∨ ∀i (Φ ∘ p') , f') ∙ ⟨ e ⟩ ↗ g)
        ext' = or-elim-eq (λ u → f' u ⟨ e ⟩) g (λ {l} → ext l) (λ {r} → snd (snd (aFill r)))

sameOtherwise :
  {Γ : Set}
  {Φ : Γ → Cof}
  {G : Γ → Set}
  (α : isFib {Γ = res Γ Φ} (G ∘ fst))
  (γ : isFib G)
  (e : OI)
  (p : Int → Γ)
  (¬∀Φ : [ ∀i (Φ ∘ p) ] → ∅)
  → ---------------
  realign {Φ = Φ} {G} α γ e p ≡ γ e p
abstract
  sameOtherwise {Γ} {Φ} {G} α γ e p ¬∀Φ =
    fibExt' {A = G} {α = realign {Φ = Φ} {G} α γ} {α' = γ} e p calc where
      
      -- A tweaked extentionality principle for fibration structures
      fibExt' : {Γ : Set}{A : Γ → Set}{α α' : isFib A}(e : OI)(p : Int → Γ)
       → ((φ : Cof)(f : [ φ ] → Π (A ∘ p))
          (a₀ : ⟦ x₁ ∈ (A (p ⟨ e ⟩)) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧) → fst (α e p φ f a₀) ≡ fst (α' e p φ f a₀))
       → α e p ≡ α' e p
      fibExt' {α = α} {α'} e p ext =
       funext (λ φ → funext (λ f → funext (λ a₀ →
         incMono (λ x → (φ , f) ∙ ⟨ ! e ⟩ ↗ x) (α e p φ f a₀) (α' e p φ f a₀) (ext φ f a₀))))

      -- The main calculation
      calc : (φ : Cof) (f : [ φ ] → Π (G ∘ p))
        (a₀ : set (G (p ⟨ e ⟩)) (_↗_ ((φ , f) ∙ ⟨ e ⟩))) →
        fst (realign {Φ = Φ} {G} α γ e p φ f a₀) ≡ fst (γ e p φ f a₀)
      calc ψ f (g , ext)  = 
        proof:
            fst (γ e p (ψ ∨ ∀i (Φ ∘ p)) f' (g , ext'))
          ≡[ cong (λ ψfext → fst (γ e p (fst (fst ψfext)) (snd (fst ψfext)) (g , snd ψfext)) ) tripleEq ]≡
            fst (γ e p ψ f (g , ext))
        qed
       where
        aFill : (∀iΦ : [ ∀i (Φ ∘ p) ]) →
          ⟦ a' ∈ ((i : Int) → G (p i)) ∣
            ((ψ , f) ↗ a') & (a' ⟨ e ⟩ ≈ g) ⟧
        aFill ∀iΦ = fill {A = G ∘ fst} e α (λ i → (p i) , ∀iΦ i) ψ f g ext
        f' : [ ψ ∨ ∀i (Φ ∘ p) ] → Π (G ∘ p)
        f' = _∪_ {φ = ψ} {ψ = ∀i (Φ ∘ p)} f (λ u → fst (aFill u)) {λ v ∀Φi → fst (snd (aFill ∀Φi)) v}
        ext' : prf ((ψ ∨ ∀i (Φ ∘ p) , f') ∙ ⟨ e ⟩ ↗ g)
        ext' = or-elim-eq (λ u → f' u ⟨ e ⟩) g (λ {l} → ext l) (λ {r} → snd (snd (aFill r)))
        pairEq : _≡_ {A = Σ ψ ∈ Cof , ([ ψ ] → Π (G ∘ p))} (ψ ∨ ∀i (Φ ∘ p) , f') (ψ , f)
        pairEq = lemma propsEq
          (or-elim (λ u → f' u ≡ f (subst [_] propsEq u)) (λ u → uip)
            (λ u → cong f (eq (fst ψ))) (λ u → ∅-elim (¬∀Φ u))) where
            lemma : {X : Set}{ψ ψ' : Cof}{f : [ ψ ] → X}{f' : [ ψ' ] → X}
              (p : ψ ≡ ψ') → ((u : [ ψ ]) → f u ≡ f' (subst [_] p u))
              → _≡_ {A = Σ ψ ∈ Cof , ([ ψ ] → X)} (ψ , f) (ψ' , f')
            lemma refl eq = Σext refl (funext eq)
            propsEq : (ψ ∨ ∀i (Φ ∘ p)) ≡ ψ
            propsEq = cofEq (propext
              (λ u → u (fst ψ) (λ{ (inl x) → x ; (inr x) → ∅-elim (¬∀Φ x)}))
              (λ u _ v → v (inl u)))
        tripleEq : ((ψ ∨ ∀i (Φ ∘ p) , f') , ext') ≡ ((ψ , f) , ext)
        tripleEq = Σext pairEq (eq ((ψ , f) ∙ ⟨ e ⟩ ↗ g))
