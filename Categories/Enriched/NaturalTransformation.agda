{-# OPTIONS --without-K --safe #-}

open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Enriched.NaturalTransformation
  {o ℓ e} {K : Setoid-Category o ℓ e} (M : Monoidal K) where

open import Level

open import Categories.Category.Monoidal.Properties M
  using (module Serialize; module Kelly's)
open import Categories.Enriched.Category M
open import Categories.Enriched.Functor M renaming (id to idF)
open import Categories.Morphism.Reasoning K
import Categories.Morphism.IsoEquiv K as IsoEquiv
open import Categories.NaturalTransformation using (ntHelper)
  renaming (NaturalTransformation to Setoid-NT)

open Setoid-Category K renaming (Obj to ObjK; id to idK)
open Commutation
open Monoidal M
open MonoidalReasoning
open Serialize

module _ {c d} {C : Category c} {D : Category d} where

  private
    module C = Category C
    module D = Category D
    module U = Underlying D

  record NaturalTransformation (F G : Functor C D) : Set (ℓ ⊔ e ⊔ c) where
    eta-equality
    private
      module F = Functor F
      module G = Functor G

    field
      comp    : ∀ X → F.₀ X U.⇒ G.₀ X
      commute : ∀ {X Y} →
        [ C [ X , Y ] ⇒ D [ F.₀ X , G.₀ Y ] ]⟨
          unitorˡ.to      ⇒⟨ unit ⊗₀ C [ X , Y ] ⟩
          comp Y ⊗₁ F.₁   ⇒⟨ D [ F.₀ Y , G.₀ Y ] ⊗₀ D [ F.₀ X , F.₀ Y ] ⟩
          D.⊚
        ≈ unitorʳ.to      ⇒⟨ C [ X , Y ] ⊗₀ unit ⟩
          G.₁ ⊗₁ comp X   ⇒⟨ D [ G.₀ X , G.₀ Y ] ⊗₀ D [ F.₀ X , G.₀ X ] ⟩
          D.⊚
        ⟩

    -- A shorthand for the components of a natural transformation:
    --
    --   α [ X ]
    --
    -- is the X-component of the family { αₓ } of "morphisms" that
    -- forms the natural transformation α.

    infixl 16 _[_]

    _[_] = comp

  open NaturalTransformation
  open D hiding (id)
  open IsoEquiv._≃_

  id : ∀ {F : Functor C D} → NaturalTransformation F F
  id {F} = record
    { comp    = λ _ → D.id
    ; commute = λ {X} {Y} → begin
      ⊚ ∘ D.id ⊗₁ F.₁ ∘ unitorˡ.to                ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
      ⊚ ∘ D.id ⊗₁ idK ∘ idK ⊗₁ F.₁ ∘ unitorˡ.to   ≈⟨ pullˡ unitˡ ⟩
      unitorˡ.from ∘ idK ⊗₁ F.₁ ∘ unitorˡ.to      ≈⟨ pullˡ unitorˡ-commute-from ⟩
      (F.₁ ∘ unitorˡ.from) ∘ unitorˡ.to           ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
      F.₁                                         ≈˘⟨ cancelʳ unitorʳ.isoʳ ⟩
      (F.₁ ∘ unitorʳ.from) ∘ unitorʳ.to           ≈˘⟨ pullˡ unitorʳ-commute-from ⟩
      unitorʳ.from ∘ F.₁ ⊗₁ idK ∘ unitorʳ.to      ≈˘⟨ pullˡ unitʳ ⟩
      ⊚ ∘ idK ⊗₁ D.id ∘ F.₁ ⊗₁ idK ∘ unitorʳ.to   ≈˘⟨ refl⟩∘⟨ pushˡ serialize₂₁ ⟩
      ⊚ ∘ F.₁ ⊗₁ D.id ∘ unitorʳ.to                ∎
    }
    where module F = Functor F

  infixr 9 _∘ᵥ_

  -- Vertical composition

  _∘ᵥ_ : {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G →
         NaturalTransformation F H
  _∘ᵥ_ {F} {G} {H} α β = record
    { comp    = λ X → α [ X ] U.∘ β [ X ]
    ; commute = λ {X} {Y} →
      begin
        ⊚ ∘ (⊚ ∘ α [ Y ] ⊗₁ β [ Y ] ∘ unitorˡ.to) ⊗₁ F.₁ ∘ unitorˡ.to
      ≈˘⟨ refl⟩∘⟨ refl⟩⊗⟨ (identityˡ ○ identityʳ) ⟩∘⟨refl ⟩
        ⊚ ∘ (⊚ ∘ α [ Y ] ⊗₁ β [ Y ] ∘ unitorˡ.to) ⊗₁ (idK ∘ F.₁ ∘ idK) ∘
        unitorˡ.to
      ≈⟨ helper (α [ Y ]) (β [ Y ]) F.₁ unitorˡ.to ⟩
        ⊚ ∘ α [ Y ] ⊗₁ (⊚ ∘ β [ Y ] ⊗₁ F.₁ ∘ unitorˡ.to) ∘ unitorˡ.to
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ commute β ⟩∘⟨refl ⟩
        ⊚ ∘ α [ Y ] ⊗₁ (⊚ ∘ G.₁ ⊗₁ β [ X ] ∘ unitorʳ.to) ∘ unitorˡ.to
      ≈˘⟨ helper (α [ Y ]) G.₁ (β [ X ]) unitorʳ.to ⟩
        ⊚ ∘ (⊚ ∘ α [ Y ] ⊗₁ G.₁ ∘ unitorˡ.to) ⊗₁ (idK ∘ β [ X ] ∘ idK) ∘
        unitorʳ.to
      ≈⟨ refl⟩∘⟨ commute α ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ⊚ ∘ (⊚ ∘ H.₁ ⊗₁ α [ X ] ∘ unitorʳ.to) ⊗₁ (idK ∘ β [ X ] ∘ idK) ∘
        unitorʳ.to
      ≈⟨ pushʳ (pushˡ ⊗-distrib-over-∘) ⟩
        (⊚ ∘ ⊚ ⊗₁ idK) ∘
        (H.₁ ⊗₁ α [ X ] ∘ unitorʳ.to) ⊗₁ (β [ X ] ∘ idK) ∘
        unitorʳ.to
      ≈⟨ ⊚-assoc ⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟩
        (⊚ ∘ idK ⊗₁ ⊚ ∘ associator.from) ∘
        (H.₁ ⊗₁ α [ X ]) ⊗₁ β [ X ] ∘ unitorʳ.to ⊗₁ idK ∘ unitorʳ.to
      ≈⟨ pullˡ (pullʳ (pullʳ assoc-commute-from)) ⟩
        (⊚ ∘ idK ⊗₁ ⊚ ∘ H.₁ ⊗₁ (α [ X ] ⊗₁ β [ X ]) ∘ associator.from) ∘
        unitorʳ.to ⊗₁ idK ∘ unitorʳ.to
      ≈˘⟨ pullʳ assoc ⟩∘⟨ to-≈ triangle-iso ⟩∘⟨refl ⟩
        ((⊚ ∘ idK ⊗₁ ⊚ ∘ H.₁ ⊗₁ (α [ X ] ⊗₁ β [ X ])) ∘ associator.from) ∘
        (associator.to ∘ idK ⊗₁ unitorˡ.to) ∘
        unitorʳ.to
      ≈⟨ pullˡ (cancelInner associator.isoʳ) ⟩
        ((⊚ ∘ idK ⊗₁ ⊚ ∘ H.₁ ⊗₁ (α [ X ] ⊗₁ β [ X ])) ∘ idK ⊗₁ unitorˡ.to) ∘
        unitorʳ.to
      ≈˘⟨ pushʳ (pushʳ split₂ʳ) ⟩∘⟨refl ⟩
        (⊚ ∘ idK ⊗₁ ⊚ ∘ H.₁ ⊗₁ (α [ X ] ⊗₁ β [ X ] ∘ unitorˡ.to)) ∘
        unitorʳ.to
      ≈˘⟨ pullˡ (refl⟩∘⟨ split₂ˡ) ⟩
        ⊚ ∘ H.₁ ⊗₁ (⊚ ∘ α [ X ] ⊗₁ β [ X ] ∘ unitorˡ.to) ∘ unitorʳ.to
      ∎
    }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H

      helper : ∀ {X₁ X₂ X₃ X₄ Y₁ Y₂ Z} (f : X₃ U.⇒ X₄) (g : Y₁ ⇒ D [ X₂ , X₃ ])
                 (h : Y₂ ⇒ D [ X₁ , X₂ ]) (i : Z ⇒ Y₁ ⊗₀ Y₂) →
               ⊚ ∘ (⊚ ∘ f ⊗₁ g ∘ unitorˡ.to) ⊗₁ (idK ∘ h ∘ idK) ∘ i  ≈
               ⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h ∘ i) ∘ unitorˡ.to
      helper f g h i = begin
          ⊚ ∘ (⊚ ∘ f ⊗₁ g ∘ unitorˡ.to) ⊗₁ (idK ∘ h ∘ idK) ∘ i
        ≈⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟩
          ⊚ ∘ (⊚ ⊗₁ idK) ∘ (f ⊗₁ g ∘ unitorˡ.to) ⊗₁ (h ∘ idK) ∘ i
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟩
          ⊚ ∘ (⊚ ⊗₁ idK) ∘ (f ⊗₁ g) ⊗₁ h ∘ unitorˡ.to ⊗₁ idK ∘ i
        ≈⟨ pullˡ ⊚-assoc ⟩
          (⊚ ∘ idK ⊗₁ ⊚ ∘ associator.from) ∘
          (f ⊗₁ g) ⊗₁ h ∘ unitorˡ.to ⊗₁ idK ∘ i
        ≈⟨ pullˡ (pullʳ (pullʳ assoc-commute-from)) ⟩
          (⊚ ∘ idK ⊗₁ ⊚ ∘ f ⊗₁ (g ⊗₁ h) ∘ associator.from) ∘
          unitorˡ.to ⊗₁ idK ∘ i
        ≈˘⟨ pullʳ assoc ⟩∘⟨ to-≈ Kelly's.coherence-iso₁ ⟩∘⟨refl ⟩
          ((⊚ ∘ idK ⊗₁ ⊚ ∘ f ⊗₁ (g ⊗₁ h)) ∘ associator.from) ∘
          (associator.to ∘ unitorˡ.to) ∘ i
        ≈⟨ pullˡ (cancelInner associator.isoʳ) ⟩
          ((⊚ ∘ idK ⊗₁ ⊚ ∘ f ⊗₁ (g ⊗₁ h)) ∘ unitorˡ.to) ∘ i
        ≈⟨ pullʳ unitorˡ-commute-to ⟩
          (⊚ ∘ idK ⊗₁ ⊚ ∘ f ⊗₁ (g ⊗₁ h)) ∘ idK ⊗₁ i ∘ unitorˡ.to
        ≈˘⟨ pushʳ (split₂ˡ ⟩∘⟨refl) ⟩
          ⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h) ∘ idK ⊗₁ i ∘ unitorˡ.to
        ≈˘⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
          ⊚ ∘ f ⊗₁ ((⊚ ∘ g ⊗₁ h) ∘ i) ∘ unitorˡ.to
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
          ⊚ ∘ f ⊗₁ (⊚ ∘ g ⊗₁ h ∘ i) ∘ unitorˡ.to
        ∎

  -- A K-enriched natural transformation induces an ordinary natural
  -- transformation on the underlying functors.

  underlyingNT : {F G : Functor C D} → NaturalTransformation F G →
                 Setoid-NT (underlyingFunctor F) (underlyingFunctor G)
  underlyingNT {F} {G} α = ntHelper (record
    { η       = comp α
    ; commute = λ {X Y} f →
      begin
        ⊚ ∘ α [ Y ] ⊗₁ (F.₁ ∘ f) ∘ unitorˡ.to
      ≈⟨ refl⟩∘⟨ split₂ʳ ⟩∘⟨refl ⟩
        ⊚ ∘ (α [ Y ] ⊗₁ F.₁ ∘ idK ⊗₁ f) ∘ unitorˡ.to
      ≈˘⟨ refl⟩∘⟨ extendˡ unitorˡ-commute-to ⟩
        ⊚ ∘ (α [ Y ] ⊗₁ F.₁ ∘ unitorˡ.to) ∘ f
      ≈⟨ extendʳ (commute α) ⟩
        ⊚ ∘ (G.₁ ⊗₁ α [ X ] ∘ unitorʳ.to) ∘ f
      ≈⟨ refl⟩∘⟨ extendˡ unitorʳ-commute-to ⟩
        ⊚ ∘ (G.₁ ⊗₁ α [ X ] ∘ f ⊗₁ idK) ∘ unitorʳ.to
      ≈˘⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        ⊚ ∘ (G.₁ ∘ f) ⊗₁ α [ X ] ∘ unitorʳ.to
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ to-≈ Kelly's.coherence-iso₃ ⟩
        ⊚ ∘ (G.₁ ∘ f) ⊗₁ α [ X ] ∘ unitorˡ.to
      ∎
    })
    where
      module F = Functor F
      module G = Functor G

  module UnderlyingNT {F} {G} α = Setoid-NT (underlyingNT {F} {G} α)

module _ {c d e} {C : Category c} {D : Category d} {E : Category e} where

  private
    module C = Category C
    module D = Category D
    module E = Category E
    module U = Underlying E
  open NaturalTransformation

  infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

  -- Left- and right-hand composition with a functor

  _∘ˡ_ : {G H : Functor C D} (F : Functor D E) →
         NaturalTransformation G H → NaturalTransformation (F ∘F G) (F ∘F H)
  _∘ˡ_ {G} {H} F α = record
    { comp    = λ X → F.₁ ∘ α [ X ]
    ; commute = λ {X Y} →
      begin
        E.⊚ ∘ (F.₁ ∘ α [ Y ]) ⊗₁ (F.₁ ∘ G.₁) ∘ unitorˡ.to
      ≈⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟩
        E.⊚ ∘ (F.₁ ⊗₁ F.₁) ∘ (α [ Y ] ⊗₁ G.₁) ∘ unitorˡ.to
      ≈˘⟨ extendʳ F.homomorphism ⟩
        F.₁ ∘ D.⊚ ∘ (α [ Y ] ⊗₁ G.₁) ∘ unitorˡ.to
      ≈⟨ refl⟩∘⟨ commute α ⟩
        F.₁ ∘ D.⊚ ∘ (H.₁ ⊗₁ α [ X ]) ∘ unitorʳ.to
      ≈⟨ extendʳ F.homomorphism ⟩
        E.⊚ ∘ (F.₁ ⊗₁ F.₁) ∘ (H.₁ ⊗₁ α [ X ]) ∘ unitorʳ.to
      ≈˘⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟩
        E.⊚ ∘ (F.₁ ∘ H.₁) ⊗₁ (F.₁ ∘ α [ X ]) ∘ unitorʳ.to
      ∎
    }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H

  _∘ʳ_ : {G H : Functor D E} →
         NaturalTransformation G H → (F : Functor C D) →
         NaturalTransformation (G ∘F F) (H ∘F F)
  _∘ʳ_ {G} {H} α F = record
    { comp    = λ X → α [ F.₀ X ]
    ; commute = λ {X Y} →
      begin
        E.⊚ ∘ α [ F.₀ Y ] ⊗₁ (G.₁ ∘ F.₁) ∘ unitorˡ.to
      ≈⟨ refl⟩∘⟨ split₂ʳ ⟩∘⟨refl ⟩
        E.⊚ ∘ (α [ F.₀ Y ] ⊗₁ G.₁ ∘ idK ⊗₁ F.₁) ∘ unitorˡ.to
      ≈˘⟨ refl⟩∘⟨ extendˡ unitorˡ-commute-to ⟩
        E.⊚ ∘ (α [ F.₀ Y ] ⊗₁ G.₁ ∘ unitorˡ.to) ∘ F.₁
      ≈⟨ extendʳ (commute α) ⟩
        E.⊚ ∘ (H.₁ ⊗₁ α [ F.₀ X ] ∘ unitorʳ.to) ∘ F.₁
      ≈⟨ refl⟩∘⟨ extendˡ unitorʳ-commute-to ⟩
        E.⊚ ∘ (H.₁ ⊗₁ α [ F.₀ X ] ∘ F.₁ ⊗₁ idK) ∘ unitorʳ.to
      ≈˘⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
        E.⊚ ∘ (H.₁ ∘ F.₁) ⊗₁ α [ F.₀ X ] ∘ unitorʳ.to
      ∎
    }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H

  -- Horizontal composition

  _∘ₕ_ : {H I : Functor D E} {F G : Functor C D} →
          NaturalTransformation H I → NaturalTransformation F G →
          NaturalTransformation (H ∘F F) (I ∘F G)
  _∘ₕ_ {_} {I} {F} {_} α β = (I ∘ˡ β) ∘ᵥ (α ∘ʳ F)
