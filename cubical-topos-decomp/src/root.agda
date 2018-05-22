----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper
--
-- Ian Orton and Andrew M. Pitts,
-- "Decomposing the Univalence Axiom"
----------------------------------------------------------------------

module root where

----------------------------------------------------------------------
-- The axioms and constructions for stricfying objects and fibrations
----------------------------------------------------------------------
open import strictness-axioms
open import strictify

----------------------------------------------------------------------
-- Relaigning fibration structures
----------------------------------------------------------------------
open import realignment

----------------------------------------------------------------------
-- The main theorems from the paper -- verifying axioms (1)-(5)
----------------------------------------------------------------------
open import decomp



----------------------------------------------------------------------
-- Note that this Agda code builds on the development accompanying
-- the paper:
--
-- Ian Orton and Andrew M. Pitts,
-- "Axioms for Modelling Cubical Type Theory in a Topos"
-- (Journal of Logical Methods in Computer Science,
--  Special Issue for CSL 2016) 
--
-- Below we list the contents of that development.
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Introducing basics (e.g. equality, products etc)
----------------------------------------------------------------------
open import prelude

----------------------------------------------------------------------
-- Impredicative universe of propositions and logic
----------------------------------------------------------------------
open import impredicative 

----------------------------------------------------------------------
-- The interval I
----------------------------------------------------------------------
open import interval

----------------------------------------------------------------------
-- Cofibrant propositions
----------------------------------------------------------------------
open import cof

----------------------------------------------------------------------
-- Fibrations
----------------------------------------------------------------------
open import fibrations

----------------------------------------------------------------------
-- Type formers: products, functions, path and identity types
----------------------------------------------------------------------
open import Data.products
open import Data.functions
open import Data.paths
open import Data.id

----------------------------------------------------------------------
-- Equivalences, quasi-inverses, contractiability, extendability etc
----------------------------------------------------------------------
open import equivs
