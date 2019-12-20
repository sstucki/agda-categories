{-# OPTIONS --without-K --safe #-}

open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Enriched.Functor {o ℓ e} {K : Setoid-Category o ℓ e}
                                   (M : Monoidal K) where

open import Level

open import Categories.Enriched.Category M
open import Categories.Functor using () renaming (Functor to Setoid-Functor)
open import Categories.Morphism.Reasoning K

open Setoid-Category K renaming (Obj to ObjK; id to idK)
open Commutation
open Monoidal M

record Functor {c d} (C : Category c) (D : Category d)
       : Set (ℓ ⊔ e ⊔ c ⊔ d) where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act₀ : C.Obj → D.Obj
    act₁ : ∀ {X Y} → C [ X , Y ] ⇒ D [ act₀ X , act₀ Y ]

    identity     : ∀ {X} → act₁ ∘ C.id ≈ D.id {act₀ X}
    homomorphism : ∀ {X Y Z} →
      [ C [ Y , Z ] ⊗₀ C [ X , Y ] ⇒ D [ act₀ X , act₀ Z ] ]⟨
        C.⊚           ⇒⟨ C [ X , Z ]                ⟩  act₁
      ≈ act₁ ⊗₁ act₁  ⇒⟨ D [ _ , _ ] ⊗₀ D [ _ , _ ] ⟩  D.⊚
      ⟩

  -- Shorthands for the functorial actions that work well as
  -- post-projections.

  ₀ = act₀
  ₁ = act₁

open Functor

id : ∀ {c} {C : Category c} → Functor C C
id {_} {C} = record
  { act₀         = λ X → X
  ; act₁         = idK
  ; identity     = identityˡ
  ; homomorphism = id-comm-sym ○ ∘-resp-≈ʳ (⟺ ⊗.identity)
  }
  where
    open HomReasoning
    open Category C

infixr 9 _∘F_

_∘F_ : ∀ {c d e} {C : Category c} {D : Category d} {E : Category e} →
       Functor D E → Functor C D → Functor C E
_∘F_ {_} {_} {_} {C} {D} {E} G F = record
  { act₀     = λ X → G.₀ (F.₀ X)
  ; act₁     = G.₁ ∘ F.₁
  ; identity = begin
      (G.₁ ∘ F.₁) ∘ C.id   ≈⟨ pullʳ F.identity ⟩
      G.₁ ∘ D.id           ≈⟨ G.identity ⟩
      E.id                 ∎
  ; homomorphism = begin
      (G.₁ ∘ F.₁) ∘ C.⊚                  ≈⟨ pullʳ F.homomorphism ⟩
      G.₁ ∘ (D.⊚ ∘ F.₁ ⊗₁ F.₁)           ≈⟨ pullˡ G.homomorphism ⟩
      (E.⊚ ∘ G.₁ ⊗₁ G.₁) ∘ F.₁ ⊗₁ F.₁    ≈˘⟨ pushʳ ⊗.homomorphism ⟩
      E.⊚ ∘ (G.₁ ∘ F.₁) ⊗₁ (G.₁ ∘ F.₁)   ∎
  }
  where
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G

    open HomReasoning
    open Category

-- A K-enriched functor induces an ordinary functor on the underlying
-- categories.

module _ {c d} {C : Category c} {D : Category d} where

  underlyingFunctor : Functor C D → Setoid-Functor (underlying C) (underlying D)
  underlyingFunctor F = record
    { F₀           = F.₀
    ; F₁           = F.₁ ∘_
    ; identity     = F.identity
    ; homomorphism = λ {_} {_} {_} {f} {g} → begin
        F.₁ ∘ C.⊚ ∘ g ⊗₁ f ∘ unitorˡ.to
      ≈⟨ pullˡ F.homomorphism ⟩
        (D.⊚ ∘ F.₁ ⊗₁ F.₁) ∘ g ⊗₁ f ∘ unitorˡ.to
      ≈˘⟨ pushʳ (pushˡ ⊗-distrib-over-∘) ⟩
        D.⊚ ∘ (F.₁ ∘ g) ⊗₁ (F.₁ ∘ f) ∘ unitorˡ.to
      ∎
    ; F-resp-≈     = ∘-resp-≈ʳ
    }
    where
      module C = Category C
      module D = Category D
      module F = Functor F
      open HomReasoning

  module UnderlyingFunctor F = Setoid-Functor (underlyingFunctor F)
