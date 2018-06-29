{-# OPTIONS --rewriting #-}
module strictify where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import strictness-axioms
open import realignment

----------------------------------------------------------------------
-- Lifting strictification to fibrations
----------------------------------------------------------------------
FibFix :
  {Γ : Set}
  {Φ : Γ → Cof}
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (iso : (x : Γ)(u : [ Φ x ]) → fst A (x , u) ≅' fst B x)
  → ---------------
  Σ A' ∈ Fib Γ ,
  Σ iso' ∈ ((x : Γ) → fst A' x ≅' fst B x) , 
  Σ rein ∈ (reindex' A' fst ≡ A) ,
    ((x : Γ)(u : [ Φ x ]) → subst (_≅' fst B x) (cong (λ A → fst A (x , u)) rein) (iso' x) ≡ iso x u)
abstract
 FibFix {Γ} {Φ} (A , α) (B , β) iso = (A' , α') , iso' , ext , iso'-ext where
   A' : Γ → Set
   A' = strictify Φ A B iso
   iso' : (x : Γ) → A' x ≅' B x
   iso' = isoB Φ A B iso
   α'-pre : isFib A'
   α'-pre = FibIso A' B iso' β
   A=A'fst = funext (restrictsToA Φ A B iso)
   α' : isFib A'
   α' = realign {Φ = Φ} {A'} (subst isFib A=A'fst α) α'-pre
   ext : reindex' (A' , α') fst ≡ (A , α)
   ext = symm (Σext A=A'fst (symm (isFixed (subst isFib A=A'fst α) α'-pre)))
   iso'-ext : (x : Γ) (u : [ Φ x ]) →
      subst (_≅' B x) (cong (λ A₁ → fst A₁ (x , u)) ext) (iso' x) ≡ iso x u
   iso'-ext x u = let uu = Σeq₂ (symm (restrictsToM Φ A B iso x u)) in 
     trans
       (Σeq₂ (symm (restrictsToM Φ A B iso x u))) -- The real proof
       (cong (λ p → subst (_≅' B x) p (iso' x))
         (uip (cong (λ A₁ → fst A₁ (x , u)) ext) (Σeq₁ (symm (restrictsToM Φ A B iso x u))))) -- fiddling with substs

-- A computation rule for when we perform a composition in the fixed
-- fibration which does not stay entirely inside the fixed portion
FibFixβ :
  {Γ : Set}
  {Φ : Γ → Cof}
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (iso : (x : Γ)(u : [ Φ x ]) → fst A (x , u) ≅' fst B x)
  (e : OI)
  (p : Int → Γ)
  (¬∀Φ : [ ∀i (Φ ∘ p) ] → ∅)
  → ---------------
  let ((A' , α') , iso' , reindex= , iso'-ext) = FibFix {Φ = Φ} A B iso in
    (a : A' (p ⟨ e ⟩)) → fst (α' e p cofFalse ∅-elim (a , λ())) ≡ _≅'_.from (iso' (p ⟨ ! e ⟩)) (fst (snd B e p cofFalse ∅-elim (_≅'_.to (iso' (p ⟨ e ⟩)) a , λ())))
abstract
 FibFixβ {Γ} {Φ} A (B , β) iso e p ¬∀Φ a =
  let ((A' , α') , iso' , reindex= , iso'-ext) = FibFix {Φ = Φ} A (B , β) iso in
  proof:
    fst (α' e p cofFalse ∅-elim (a , λ()))
      ≡[ cong {A = (ψ : Cof)(f : [ ψ ] → Π (A' ∘ p)) → (⟦ a₀ ∈ A' (p ⟨ e ⟩) ∣ (ψ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧) → ⟦ a₁ ∈ A' (p ⟨ ! e ⟩) ∣ (ψ , f) ∙ ⟨ ! e ⟩ ↗ a₁ ⟧}
           {B = A' (p ⟨ ! e ⟩)} (λ α'ep → fst (α'ep cofFalse ∅-elim (a , λ()))) (sameOtherwise _ (FibIso A' B iso' β) e p ¬∀Φ) ]≡
    fst (FibIso A' B iso' β e p cofFalse ∅-elim (a , λ()))
      ≡[ FibIsoβ A' B iso' β e p a ]≡
    _
  qed
    where
      FibIsoβ :
        {Γ : Set}
        (A B : Γ → Set)
        (iso : (x : Γ) → A x ≅' B x)
        (β : isFib B)
        (e : OI)
        (p : Int → Γ)
        (a : A (p ⟨ e ⟩))
        → ---------------
        fst (FibIso A B iso β e p cofFalse ∅-elim (a , λ())) ≡ _≅'_.from (iso (p ⟨ ! e ⟩)) (fst (β e p cofFalse ∅-elim (_≅'_.to (iso (p ⟨ e ⟩)) a , λ())))
      FibIsoβ A B iso β e p a =
        cong (λ f,ext →  _≅'_.from (iso (p ⟨ ! e ⟩)) (fst (β e p cofFalse (fst f,ext) (_≅'_.to (iso (p ⟨ e ⟩)) a , snd f,ext))))
          (Σext (funext (λ())) (funext λ()))
