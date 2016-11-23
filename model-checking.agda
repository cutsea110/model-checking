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
open import Relation.Nullary renaming (¬_ to !_)

-- Definition 2.1
data Form : Set where
  Atom : ℕ → Form
  ¬_ : Form → Form
  _∧_ : Form → Form → Form
  _∨_ : Form → Form → Form
  _⇒_ : Form → Form → Form

Form' : Pred Form lzero
Form' = const ⊤

-- _⊨_ is not strictly positive, because of ¬_ and _⇒_
data _⊨_ (V : Pred Form lzero) : Form → Set where
  Atom : ∀ {p} → p ∈ V → V ⊨ p
  ¬_   : ∀ {φ} → ! (V ⊨ φ) → V ⊨ (¬ φ)
  _∧_  : ∀ {φ ψ} → V ⊨ φ ⊗ V ⊨ ψ → V ⊨ (φ ∧ ψ)
  _∨_  : ∀ {φ ψ} → V ⊨ φ ⊕ V ⊨ ψ → V ⊨ (φ ∨ ψ)
  _⇒_  : ∀ {φ ψ} → (V ⊨ φ → V ⊨ ψ) → V ⊨ (φ ⇒ ψ)
