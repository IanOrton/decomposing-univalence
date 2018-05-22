{-# OPTIONS --rewriting #-}
module strictness-axioms where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations

----------------------------------------------------------------------
-- Strictifying
----------------------------------------------------------------------
postulate
 reIm :
  (φ : Cof)
  (A : [ φ ] → Set)
  (B : Set)
  (m : (u : [ φ ]) → A u ≅' B)
  -> ----------------------
  Σ B' ∈ Set , Σ m' ∈ B' ≅' B , ((u : [ φ ]) → (A u , m u) ≡ (B' , m'))

strictify :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (m : (x : Γ)(u : [ Φ x ]) → A (x , u) ≅' B x)
  -> ----------------------
  Γ → Set
strictify Φ A B m x = fst (reIm (Φ x)(λ u → A (x , u)) (B x) (m x))

isoB :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (m : (x : Γ)(u : [ Φ x ]) → A (x , u) ≅' B x)
  (x : Γ)
  -> ----------------------
  strictify Φ A B m x ≅' B x
isoB Φ A B m x = fst (snd (reIm (Φ x)(λ u → A (x , u)) (B x) (m x)))
  
restrictsToA :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (m : (x : Γ)(u : [ Φ x ]) → A (x , u) ≅' B x)
  (x : res Γ Φ)
  -> ----------------------
  A x ≡ strictify Φ A B m (fst x)
restrictsToA Φ A B m (x , u) = Σeq₁ (snd (snd (reIm (Φ x)(λ u → A (x , u)) (B x) (m x))) u)
  
restrictsToM :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (m : (x : Γ)(u : [ Φ x ]) → A (x , u) ≅' B x)
  (x : Γ)
  (u : [ Φ x ])
  -> ----------------------
  (A (x , u) , m x u) ≡ (strictify Φ A B m x , isoB Φ A B m x)
restrictsToM Φ A B m x u = snd (snd (reIm (Φ x)(λ u → A (x , u)) (B x) (m x))) u
