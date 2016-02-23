{- Proof of the Universal Property of Our Fold -}

module FoldUniv where

open import Function using (id)
open import Data.Unit using (⊤ ; tt) public
open import Data.Empty using (⊥) public
open import Data.Sum using (_⊎_; [_,_]; inj₁ ; inj₂) public
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.List
open import Data.List.Any as Any
open import Data.Product
open Any.Membership-≡ hiding (_⊆_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data PolyF : Set where
  Id    : PolyF
  K1    : PolyF
  Kℕ    : PolyF
  KB    : PolyF
  _∔_   : (F : PolyF) → (G : PolyF) → PolyF
  _⋆_   : (F : PolyF) → (G : PolyF) → PolyF

infixr 30 _⋆_
infixr 20 _∔_

⟦_⟧ : PolyF → Set → Set
⟦_⟧ Id A      = A
⟦_⟧ K1 A     = ⊤
⟦_⟧ Kℕ A     = ℕ
⟦_⟧ KB A     = Bool
⟦_⟧ (F ∔ G) A = ⟦ F ⟧ A ⊎ ⟦ G ⟧ A
⟦_⟧ (F ⋆ G) A = ⟦ F ⟧ A × ⟦ G ⟧ A

fmap : ∀ {A B} F → (A → B) → ⟦ F ⟧ A → ⟦ F ⟧ B
fmap Id f = f
fmap K1 f = id
fmap Kℕ f = id
fmap KB f = id
fmap (F ∔ G) f =
  Data.Sum.map (fmap F f) (fmap G f)
fmap (F ⋆ G) f =
  Data.Product.map (fmap F f) (fmap G f)

Algebras : List PolyF → Set → Set
Algebras []       A = ⊤
Algebras (F ∷ Fs) A = (⟦ F ⟧ A → A) × Algebras Fs A

extract : {F : PolyF} {Fs : List PolyF} {A : Set}
          → F ∈ Fs → Algebras Fs A → (⟦ F ⟧ A → A)
extract (here refl) (f , _ ) = f
extract (there f∈ ) (f , fs) = extract f∈ fs

data μ (Fs : List PolyF) : Set where
  In : ∀ {F} → F ∈ Fs → ⟦ F ⟧ (μ Fs) → μ Fs

mutual
  fold : ∀ Fs {A} → Algebras Fs A → μ Fs → A
  fold Fs fs (In {F} F∈ x) = extract F∈ fs (mapFold Fs fs F x)

  mapFold : (Fs : List PolyF) {A : Set}
          → Algebras Fs A → (G : PolyF) → ⟦ G ⟧ (μ Fs) → ⟦ G ⟧ A
  mapFold Fs fs Id       x          = fold Fs fs x
  mapFold Fs fs K1       b          = b
  mapFold Fs fs Kℕ       b          = b
  mapFold Fs fs KB       b          = b
  mapFold Fs fs (G ∔ G') (inj₁ xs)  = inj₁ (mapFold Fs fs G xs)
  mapFold Fs fs (G ∔ G') (inj₂ xs)  = inj₂ (mapFold Fs fs G' xs)
  mapFold Fs fs (G ⋆ G') (xs , xs') = mapFold Fs fs G xs , mapFold Fs fs G' xs'

mutual

 fold-universal : (Fs : List PolyF) → {A : Set}
                → (h : μ Fs → A) → (fs : Algebras Fs A)
                → (∀ F → (F∈ : F ∈ Fs) →
                   ∀ xs → h (In F∈ xs) ≡ extract F∈ fs (fmap F h xs))
                → (∀ xs → h xs ≡ fold Fs fs xs)
 fold-universal Fs h fs hom (In {F} F∈ xs)
   rewrite hom F F∈ xs = cong (extract F∈ fs) (mapFold-univ Fs F h fs hom xs)

 mapFold-univ : (Fs : List PolyF) (G : PolyF)
              → ∀ {A : Set}
              → (h : μ Fs → A) → (fs : Algebras Fs A)
              → (∀ F → (F∈ : F ∈ Fs) →
                   ∀ xs → h (In F∈ xs) ≡ extract F∈ fs (fmap F h xs))
              → (Gxs : ⟦ G ⟧ (μ Fs))
              → fmap G h Gxs ≡ mapFold Fs fs G Gxs
 mapFold-univ Fs Id h fs hom xs = fold-universal Fs h fs hom xs
 mapFold-univ Fs K1 h fs hom tt = refl
 mapFold-univ Fs Kℕ h fs hom n = refl
 mapFold-univ Fs KB h fs hom b = refl
 mapFold-univ Fs (G₁ ∔ G₂) h fs hom (inj₁ x) = cong inj₁ (mapFold-univ Fs G₁ h fs hom x)
 mapFold-univ Fs (G₁ ∔ G₂) h fs hom (inj₂ y) = cong inj₂ (mapFold-univ Fs G₂ h fs hom y)
 mapFold-univ Fs (G₁ ⋆ G₂) h fs hom (x , y)
     rewrite mapFold-univ Fs G₁ h fs hom x | mapFold-univ Fs G₂ h fs hom y = refl
