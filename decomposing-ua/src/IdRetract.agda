{-# OPTIONS --without-K #-}

open import Agda.Primitive using (Level)
open import PropEqWithoutK
open import Prelude

----------------------------------------------------------------------
-- Any retract of the identity type is equivalent to the identity type
----------------------------------------------------------------------
IdRetract :
  {l l' : Level}
  {A : Set l}
  (P : A → A → Set l')
  (f : {x y : A} → x ≡ y → P x y)
  (g : {x y : A} → P x y → x ≡ y)
  (f∘g : {x y : A}(p : P x y) → f (g p) ≡ p)
  → ∀ {x y} → isEquiv (f {x} {y})
IdRetract {A = A} P f g f∘g = isHAE→isEquiv f (Qinv→isHAE f (g , g∘f , f∘g)) where
  trans-sym : {x y : A}(p : x ≡ y) → trans p (sym p) ≡ refl
  trans-sym refl = refl
  g' : {x y : _} →  P x y → x ≡ y
  g' p = trans (g p) (sym (g (f refl)))
  g'∘f : {x y : A}(p : x ≡ y) → g' (f p) ≡ p
  g'∘f refl = trans-sym (g (f refl))
  g∘f : {x y : A}(p : x ≡ y) → g (f p) ≡ p
  g∘f p = trans (trans (sym (g'∘f (g (f p)))) (cong g' (f∘g (f p)))) (g'∘f p)
