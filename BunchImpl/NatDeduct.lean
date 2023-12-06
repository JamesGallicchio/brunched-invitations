import BunchImpl.Subbunch
import BunchImpl.Equiv

namespace BunchImpl

open Typ Bunch

set_option hygiene false in section
local infix:35 " ⊢ " => NDEntails

inductive NDEntails {P : Type u} : Bunch P → Typ P → Prop
| id {φ : P} :
      atom φ ⊢ atom φ
| equiv :
    Γ ≈ Δ →
    Γ ⊢ φ →
      Δ ⊢ φ
| weaken (Γ : BunchWithHole P) :
    Γ Δ ⊢ φ →
      Γ (Δ;ᵇ Δ') ⊢ φ
| contract (Γ : BunchWithHole P) :
    Γ (Δ;ᵇ Δ) ⊢ φ →
      Γ Δ ⊢ φ
| empI : cunit ⊢ emp
| empE (Γ : BunchWithHole P) :
    Γ cunit ⊢ χ   →
    Δ ⊢ emp →
      Γ Δ ⊢ χ
| dandyI {φ ψ : Typ P} :
    Γ,ᵇ φ ⊢ ψ →
      Γ ⊢ [bi| φ -* ψ ]
| dandyE :
    Γ ⊢ [bi| φ -* ψ ] →
    Δ ⊢ φ →
      Γ,ᵇ Δ ⊢ ψ
| starI :
    Γ ⊢ φ →
    Δ ⊢ ψ →
      Γ,ᵇ Δ ⊢ [bi| φ * ψ ]
| starE {φ ψ : Typ P} (Γ : BunchWithHole P) :
    Γ (φ,ᵇ ψ) ⊢ χ →
    Δ ⊢ [bi| φ * ψ ] →
      Γ Δ ⊢ χ
| trI (Γ : BunchWithHole P) :
    Γ sunit ⊢ χ →
    Δ ⊢ tr →
      Γ Δ ⊢ χ
| trE :
      sunit ⊢ tr
| arrI {φ : Typ P} :
    Γ;ᵇ φ ⊢ ψ →
      Γ ⊢ [bi| φ → ψ ]
| arrE :
    Γ ⊢ [bi| φ → ψ ] →
    Δ ⊢ φ →
      Γ;ᵇ Δ ⊢ ψ
| andI :
    Γ ⊢ φ →
    Γ ⊢ ψ →
      Γ ⊢ [bi| φ ∧ ψ ]
| andE {φ ψ : Typ P} (Γ : BunchWithHole P) :
    Γ (φ;ᵇ ψ) ⊢ χ →
    Δ ⊢ [bi| φ ∧ ψ ] →
      Γ Δ ⊢ χ
| orI1 :
    Γ ⊢ φ₁ →
      Γ ⊢ [bi| φ₁ ∨ φ₂]
| orI2 :
    Γ ⊢ φ₂ →
      Γ ⊢ [bi| φ₁ ∨ φ₂]
| orE {φ₁ φ₂ : Typ P} (Γ : BunchWithHole P) (Δ : Bunch P):
    Δ ⊢ [bi| φ₁ ∨ φ₂ ] →
    Γ φ ⊢ χ →
    Γ ψ ⊢ χ →
      Γ Δ ⊢ χ
| flsE :
    Γ ⊢ fls →
      Γ ⊢ φ
end

scoped infix:35 " ⊢ " => NDEntails

namespace NDEntails

attribute [simp]
  id equiv weaken contract
  empI empE dandyI dandyE starI starE
  trI trE arrI arrE andI andE orI1 orI2 orE flsE
theorem id_admissible {φ : Typ P} : φ ⊢ φ := by
  induction φ <;> aesop

def cut_admissible (Γ : BunchWithHole P) (Δ : Bunch P) (φ : Typ P)
          (D : Γ φ ⊢ ψ) (E : Δ ⊢ φ) : Γ Δ ⊢ ψ
  :=
  match Γ, Δ, φ, D, E with
  | _, _, _, D, .id => D
  | _, _, _, D, .equiv E₁ E₂ => by
    apply NDEntails.equiv
    · apply BunchEquiv.subbunch _ E₁
    · apply cut_admissible _ _ _ D E₂
  | _, _, _, D, .weaken _ E' => by
    rw [←BunchWithHole.comp_def]
    apply NDEntails.weaken
    rw [BunchWithHole.comp_def]
    apply cut_admissible _ _ _ D E'
  | _, _, _, D, .contract _ E' => by
    rw [←BunchWithHole.comp_def]
    apply NDEntails.contract
    rw [BunchWithHole.comp_def]
    apply cut_admissible _ _ _ D E'
  | _, _, emp, D, .empE _ E₁ E₂ => by
    rw [← BunchWithHole.comp_def]
    apply NDEntails.empE
    · rw [BunchWithHole.comp_def]
      apply cut_admissible _ _ emp D E₂
    · exact E₁
  | _, _, _, .dandyI E', _ => by
    simp at D
    apply dandyI
    sorry
  | _, _, _, _, .dandyE Δ₁ _ _ Δ₂ D₁ D₂ => by
    simp at D₁
    sorry
  | _, _, _, _, _ => sorry
termination_by _ Γ Δ φ D E => 0
decreasing_by sorry
