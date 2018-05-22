----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper "Decomposing the
-- Univalence Axiom".
--
-- This development builds on the code for the paper "Axioms for
-- Modelling Cubical Type Theory in a Topos" (CSL Special Issue
-- version). 
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module decomp where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import Data.paths

open import strictify
open import realignment

----------------------------------------------------------------------
-- Some preliminaries
----------------------------------------------------------------------
<_,id> : {Γ : Set} → Γ → Int → Γ × Int
< x ,id> i = (x , i)

i=OI : {Γ : Set} → Γ × Int → Cof
i=OI (x , i) = (i ≈O) ∨ (i ≈I)

¬∀i=OI : [ ∀i (λ i → (i ≈O) ∨ (i ≈I)) ] → ∅
¬∀i=OI ∀i=OI = O≠I (subst prf O≈O≡O≈I refl) where
  cases : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → prf ((O ≈ i) or ¬ (O ≈ i))
  cases (inl i=O) = ∣ inl (symm i=O) ∣
  cases (inr i=I) = ∣ inr (λ O=i → ∅-elim (O≠I (trans i=I O=i))) ∣
  O≈O≡O≈I : (O ≈ O) ≡ (O ≈ I)
  O≈O≡O≈I = cntd' (λ i → O ≈ i) (λ i → ∥∥-elim cases (λ _ _ → eq ((O ≈ i) or ¬ (O ≈ i))) (∀i=OI i)) O

----------------------------------------------------------------------
-- The notion of paths in the universe that we work with
----------------------------------------------------------------------
IdU : {Γ : Set} → Fib Γ → Fib Γ → Set₁
IdU {Γ} Aα Bβ = Σ Pρ ∈ Fib (Γ × Int) , (reindex' Pρ (λ x → x , O) ≡ Aα) × (reindex' Pρ (λ x → x , I) ≡ Bβ)

----------------------------------------------------------------------
-- The weaker notion of path equality in the universe
----------------------------------------------------------------------
IdU-weak : {Γ : Set} → Fib Γ → Fib Γ → Set₁
IdU-weak {Γ} (A , α) (B , β) = Σ Pρ ∈ Fib (Γ × Int) , (A ≅ (fst Pρ ∘ (λ x → x , O))) × (B ≅ (fst Pρ ∘ (λ x → x , I)))

----------------------------------------------------------------------
-- Defining the A ⊻ B construction
----------------------------------------------------------------------
data Tag : Set where
  i=O : Tag; i=I : Tag
decode : Set → Set → Tag → Set
decode A _ i=O = A
decode _ B i=I = B

_⊻_ : {Γ : Set}(A B : Fib Γ) → Fib (res (Γ × Int) i=OI)
_⊻_ {Γ} (A , α) (B , β) = A∨B , μ where
  A∨B : res (Γ × Int) i=OI → Set
  A∨B ((x , i) , u) = decode (A x) (B x) (OI-elim (λ{ (inl x₁) → i=O ; (inr x₁) → i=I }) u)
  μ : isFib A∨B
  μ e p = OI-elim cases (snd (p I)) where
    pZero : Int → Ω
    pZero i = snd (fst (p i)) ≈ O
    pOne : Int → Ω
    pOne i = snd (fst (p i)) ≈ I
    lem : (i : Int) → pZero i ≡ pZero I
    lem = cntd' pZero dec where
      dec : (i : Int) → prf (pZero i or ¬ (pZero i))
      dec i = ∥∥-elim
        (λ{ (inl x) → ∣ inl x ∣ ; (inr pi=I) → ∣ inr (λ pi=O → O≠I (trans pi=I (symm pi=O))) ∣ })
        (λ x x → eq (pZero i or ¬ (pZero i))) (snd (p i))
    lem' : (i : Int) → pOne i ≡ pOne I
    lem' = cntd' pOne dec where
      dec : (i : Int) → prf (pOne i or ¬ (pOne i))
      dec i = ∥∥-elim
        (λ{ (inl pi=O) → ∣ inr (λ pi=I → O≠I (trans pi=I (symm pi=O))) ∣ ; (inr pi=I) → ∣ inl pi=I ∣ })
        (λ x x → eq (pOne i or ¬ (pOne i))) (snd (p i))
    cases : prf (pZero I) ⊎ prf (pOne I) → Comp e (A∨B ∘ p)
    cases (inl pI=O) = subst (Comp e) (symm Cp=Ap) (α e (fst ∘ fst ∘ p)) where
      pi=O : (i : Int) → prf (pZero i)
      pi=O i = subst prf (symm (lem i)) pI=O
      etaExp : (i : Int) → p i ≡ ((fst (fst (p i)) , O) , ∣ inl refl ∣)
      etaExp i = Σext (Σext refl (pi=O i)) (eq ((O ≈ O) or (O ≈ I)))
      Cp=Ap : A∨B ∘ p ≡  A ∘ fst ∘ fst ∘ p
      Cp=Ap = funext (λ i → cong A∨B (etaExp i))
    cases (inr pI=I) = subst (Comp e) (symm Cp=Bp) (β e (fst ∘ fst ∘ p)) where
      pi=I : (i : Int) → prf (snd (fst (p i)) ≈ I)
      pi=I i = subst prf (symm (lem' i)) pI=I
      etaExp : (i : Int) → p i ≡ ((fst (fst (p i)) , I) , ∣ inr refl ∣)
      etaExp i = Σext (Σext refl (pi=I i)) (eq ((I ≈ O) or (I ≈ I)))
      Cp=Bp : A∨B ∘ p ≡  B ∘ fst ∘ fst ∘ p
      Cp=Bp = funext (λ i → cong A∨B (etaExp i))

-- Lifting isos to A ⊻ B (also written _⊻_ is the paper)
mk-iso :
  {Γ : Set}
  (A B : Fib Γ)
  (P : IdU-weak A B)
  → --------------------
  (x : Γ × Int) (u : [ i=OI x ]) → fst (A ⊻ B) (x , u) ≅' fst (fst P) x
mk-iso A B (P , isoA , isoB) (x , i) u = OI-elim-dep {B = λ u → fst (A ⊻ B) ((x  , i) , u) ≅' fst P (x , i)} cases u where
    cases : (v : (i ≡ O) ⊎ (i ≡ I)) → fst (A ⊻ B) ((x , i) , ∣ v ∣) ≅' fst P (x , i)
    cases (inl refl) = isoA x
    cases (inr refl) = isoB x

----------------------------------------------------------------------
-- Improving these misaligned paths to proper paths
----------------------------------------------------------------------
IdU-improve :
  {Γ : Set}
  {A B : Fib Γ}
  → --------------------
  IdU-weak A B → IdU A B
IdU-improve {Γ} {A} {B} (P , isoA , isoB) = fst P' , reindA , reindB where
  P' = FibFix {Φ = i=OI} (A ⊻ B) P (mk-iso A B (P , isoA , isoB))
  reindA : reindex' (fst P') (λ x → x , O) ≡ A
  reindA = cong (λ A → reindex' A λ x → ((x , O) , ∣ inl refl ∣)) (fst (snd (snd P')))
  reindB : reindex' (fst P') (λ x → x , I) ≡ B
  reindB = cong (λ A → reindex' A λ x → ((x , I) , ∣ inr refl ∣)) (fst (snd (snd P')))

----------------------------------------------------------------------
-- Isopath/Isovalence
----------------------------------------------------------------------
isovalence :
  {Γ : Set}
  {A B : Fib Γ}
  (iso : (x : Γ) → fst A x ≅' fst B x)
  → --------------------
  IdU A B
isovalence {Γ} {A} {B} iso = IdU-improve (reindex' B fst , iso , id-iso) where
  id-iso : (x : Γ) → fst B x ≅' fst B x
  id-iso x = record { to = id ; from = id ; inv₁ = refl ; inv₂ = refl } 


----------------------------------------------------------------------
-- The corresponding beta rule
----------------------------------------------------------------------
coerce : {Γ : Set}{A B : Fib Γ} → IdU A B → (x : Γ) → fst A x → fst B x
coerce ((P , ρ) , eqA , eqB) x a = coe PI=B (f (coe (symm PO=A) a)) where
  f : P (x , O) → P (x , I)
  f a = fst (ρ O' < x ,id> cofFalse ∅-elim (a , (λ ())))
  PO=A : P (x , O) ≡ _
  PO=A = cong (λ A → fst A x) eqA
  PI=B : P (x , I) ≡ _
  PI=B = cong (λ A → fst A x) eqB

isovalenceβ :
  {Γ : Set}
  {A B : Fib Γ}
  (iso : (x : Γ) → fst A x ≅' fst B x)
  → --------------------
  (x : Γ)(a : fst A x) → _≅'_.to (iso x) a ~ coerce (isovalence {A = A} {B} iso) x a
isovalenceβ {Γ} {A} {B} iso x a = subst (_≅'_.to (iso x) a ~_) (symm calc) (trivPath B (_≅'_.to (iso x) a)) where

  -- Name some of the objects we'll be manipulating in the proof
  PρEqs = FibFix {Φ = i=OI} (A ⊻ B) (reindex' B fst) (mk-iso A B _)
  P = fst (fst PρEqs)
  ρ = snd (fst PρEqs)
  iso' = fst (snd PρEqs)
  rein = fst (snd (snd PρEqs))
  iso'-ext = snd (snd (snd PρEqs))

  -- Proofs that the endpoints match up
  PO=A : P (x , O) ≡ _
  PO=A = cong (λ A → fst A x) (cong (λ A → reindex' A λ x → ((x , O) , ∣ inl refl ∣)) rein)
  PI=B : P (x , I) ≡ _
  PI=B = cong (λ A → fst A x) (cong (λ A → reindex' A λ x → ((x , I) , ∣ inr refl ∣)) rein)
  p = coe (symm PO=A) a

  -- The new iso is just the old one at i=O
  coe-iso'-atO : (_≅'_.to (iso' (x , O)) p) ≡ _≅'_.to (iso x) a
  coe-iso'-atO = proof:
    _≅'_.to (iso' (x , O)) p
      ≡[ iso-lemma _ PO=A PO='A a ]≡
    _≅'_.to (subst (_≅' fst B x) PO='A (iso' (x , O))) a
      ≡[ cong (λ iso → _≅'_.to iso a) (iso'-ext (x , O) ∣ inl refl ∣) ]≡
    _≅'_.to (iso x) a
   qed
    where
      PO='A = cong (λ A → fst A ((x , O) , ∣ inl refl ∣)) rein
      iso-lemma : {A' A B : Set}(iso : A ≅' B)(p p' : A ≡ A')(a : A') → _≅'_.to iso (coe (symm p) a) ≡ _≅'_.to (subst (_≅' B) p' iso) a
      iso-lemma _ refl refl _ = refl

  -- The new iso is just the identity at i=I 
  coe-iso'-atI : (b : fst B x) → coe PI=B (_≅'_.from (iso' (x , I)) b) ≡ b
  coe-iso'-atI b = proof:
    coe PI=B (_≅'_.from (iso' (x , I)) b)
      ≡[ iso-lemma _ PI=B PI='B b ]≡
    _≅'_.from (subst (_≅' fst B x) PI='B (iso' (x , I))) b
      ≡[ cong (λ iso → _≅'_.from iso b) (iso'-ext (x , I) ∣ inr refl ∣) ]≡
    b
   qed
    where
      PI='B = cong (λ A → fst A ((x , I) , ∣ inr refl ∣)) rein
      iso-lemma : {A A' B : Set}(iso : A ≅' B)(p p' : A ≡ A')(b : B) → coe p (_≅'_.from iso b) ≡ _≅'_.from (subst (_≅' B) p' iso) b
      iso-lemma _ refl refl _ = refl

  -- The main calculation
  calc : coerce (isovalence {A = A} {B} iso) x a ≡ trivComp B O' x (_≅'_.to (iso x) a)
  calc =
    proof:
      coerce (isovalence {A = A} {B} iso) x a
        ≡[ refl ]≡
      coe PI=B (fst (ρ O' < x ,id> cofFalse ∅-elim (p , λ ())))
        ≡[ cong (coe PI=B) (FibFixβ (A ⊻ B) (reindex' B fst) (mk-iso A B _) O' < x ,id> ¬∀i=OI p) ]≡
      coe PI=B (_≅'_.from (iso' (x , I)) (trivComp B O' x (_≅'_.to (iso' (x , O)) p)))
        ≡[ coe-iso'-atI _ ]≡
      trivComp B O' x (_≅'_.to (iso' (x , O)) p)
        ≡[ cong (trivComp B O' x) coe-iso'-atO ]≡
      trivComp B O' x (_≅'_.to (iso x) a)
    qed

  
----------------------------------------------------------------------
-- Contraction
----------------------------------------------------------------------
C : {Γ : Set} → (Γ → Set) → Γ × Int → Set
C A (x , i) = [ i ≈O ] → A x

CFib' :
  {Γ : Set}
  (A : Γ → Set)
  (α : isFib A)
  (c : Contr A)
  → --------------
  isFib (C A)
CFib' A α c e p φ f a₀ = a₁ , extends where
  ext = contr2ext α c
  a₁' : (v : [ snd (p ⟨ ! e ⟩) ≈O ]) → ⟦ a ∈ A (fst (p ⟨ ! e ⟩)) ∣ (φ , (λ z → f z ⟨ ! e ⟩ v)) ↗ a ⟧
  a₁' v = ext (fst (p ⟨ ! e ⟩)) φ (λ u → f u ⟨ ! e ⟩ v)
  a₁ : C A (p ⟨ ! e ⟩)
  a₁ v = fst (a₁' v)
  extends : prf ((φ , f) ∙ ⟨ ! e ⟩ ↗ a₁)
  extends u = funext λ v → snd (a₁' v) u

Unit' : {Γ : Set} → Fib Γ
Unit' = ((λ _ → Unit) , FibUnit)

contract :
  {Γ : Set}
  (A : Fib Γ)
  (c : Contr (fst A))
  → --------------
  IdU A Unit'
contract {Γ} (A , α) c = IdU-improve ((C A , CFib' A α c) , isoA , iso1) where
  isoA : (x : Γ) → A x ≅' (O ≡ O → A x)
  isoA x = record { to = λ z _ → z ; from = λ z → z refl ; inv₁ = refl ; inv₂ = funext λ _ → funext λ{ refl → refl } }
  iso1 : (x : Γ) → Unit ≅' (I ≡ O → A x)
  iso1 x = record { to = λ tt p → ∅-elim (O≠I (symm p)) ; from = λ _ → tt ;
    inv₁ = refl ; inv₂ = funext λ _ → funext λ p → ∅-elim (O≠I (symm p)) }
