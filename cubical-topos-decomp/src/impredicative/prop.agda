----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper
--
-- Ian Orton and Andrew M. Pitts,
-- "Axioms for Modelling Cubical Type Theory in a Topos"
-- (Journal of Logical Methods in Computer Science, Special Issue for CSL 2016) 
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

{-# OPTIONS --type-in-type #-}
-- the following definition relies on type-in-type,
-- which is switched on only in this module

module impredicative.prop where

open import prelude

record Ω : Set where
  constructor prop
  field
    prf : Set
    equ : (u v : prf) → u ≡ v

open Ω public

eq : (P : Ω){u v : prf P} → u ≡ v
eq P {u} {v} = equ P u v
