{-# OPTIONS --no-positivity-check #-}
module model-checking where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List
open import Data.Nat
open import Data.Product renaming (_×_ to _⊗_)
open import Data.Sum renaming (_⊎_ to _⊕_)
open import Function using (_∘_; const)
open import Relation.Unary using (_∈_; Pred; _⊆_)

-- Definition 2.1
data Form : Set where
  Atom : ℕ → Form
  ¬_ : Form → Form
  _∧_ : Form → Form → Form
  _∨_ : Form → Form → Form
  _⇒_ : Form → Form → Form

Form' : Pred Form lzero
Form' = const ⊤

data _⊨_ (V : Pred Form lzero) : Form → Set

_⊭_ : Pred Form lzero → Form → Set
V ⊭ φ = V ⊨ φ → ⊥

-- _⊨_ is not strictly positive, because of neg and imp
data _⊨_ (V : Pred Form lzero) where
  atom : ∀ {p}   → p ∈ V → V ⊨ p
  neg  : ∀ {φ}   → V ⊭ φ → V ⊨ (¬ φ)
  conj : ∀ {φ ψ} → V ⊨ φ ⊗ V ⊨ ψ → V ⊨ (φ ∧ ψ)
  disj : ∀ {φ ψ} → V ⊨ φ ⊕ V ⊨ ψ → V ⊨ (φ ∨ ψ)
  imp  : ∀ {φ ψ} → (V ⊨ φ → V ⊨ ψ) → V ⊨ (φ ⇒ ψ)
