----------------------------------------------------------------------
-- Reproducing code from the Agda standrad library to ensure that
-- we're not secretly using Axiom K
----------------------------------------------------------------------
{-# OPTIONS --without-K #-}

module PropEqWithoutK where

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

-- {-# BUILTIN EQUALITY _≡_ #-}
-- {-# BUILTIN REFL refl #-}


sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

module ≡-Reasoning {a} {A : Set a} where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl
