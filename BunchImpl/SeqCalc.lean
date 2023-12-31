import BunchImpl.Subbunch
import BunchImpl.Equiv

namespace BunchImpl

open Typ Bunch

set_option hygiene false in section
local infix:35 " ⊢ " => SeqEntails

inductive SeqEntails {P : Type u} : Bunch P → Typ P → Prop
| id_atom {A : P} : /-prop-/
      atom A ⊢ atom A
| equiv :
    Γ ≈ Δ →
    Γ ⊢ C →
      Δ ⊢ C
| weaken {Γ : BunchWithHole P} :
    Γ Δ ⊢ C →
      Γ (Δ;ᵇ Δ') ⊢ C
| contract {Γ : BunchWithHole P} :
    Γ (Δ;ᵇ Δ) ⊢ C →
      Γ Δ ⊢ C
| empR : cunit ⊢ emp /-not sure about this-/
| empL {Γ : BunchWithHole P} : /- Not sure about this one -/
    Γ cunit ⊢ C →
      Γ (prop emp) ⊢ C
| dandyR {Γ : Bunch P} {A B : Typ P} :
    Γ,ᵇ A ⊢ B →
      Γ ⊢ [bi| A -* B ]
| dandyL {Δ : Bunch P} {Γ : BunchWithHole P} {A B C : Typ P} :
    Δ ⊢ A →
    Γ B ⊢ C →
      Γ (Δ,ᵇ [bi| A -* B ]) ⊢ C
| starR {Γ Δ} {A B : Typ P} :
    Γ ⊢ A →
    Δ ⊢ B →
      Γ,ᵇ Δ ⊢ [bi| A * B ]
| starL {Γ : BunchWithHole P} {A B : Typ P} :
    Γ (A,ᵇ B) ⊢ C →
      Γ (prop [bi| A * B]) ⊢ C
| trR : /-not sure about this-/
    sunit ⊢ tr
| trL {Γ : BunchWithHole P} : /-not sure about this-/
    Γ sunit ⊢ C →
      Γ (prop tr) ⊢ C
| arrR {Γ} {A B : Typ P} :
    Γ;ᵇ A ⊢ B →
      Γ ⊢ [bi| A → B ]
| arrL {Γ : BunchWithHole P} {Δ} {A B C : Typ P} :
    Δ ⊢ A →
    Γ (Δ;ᵇ B) ⊢ C →
      Γ (Δ;ᵇ [bi| A → B ]) ⊢ C
| andR {Γ} {A B} :
    Γ ⊢ A →
    Γ ⊢ B →
      Γ ⊢ [bi| A ∧ B ]
| andL {Γ : BunchWithHole P} {A B C: Typ P} :
    Γ (A;ᵇ B) ⊢ C →
      Γ [bi| A ∧ B ] ⊢ C
| orR1 {Γ} {A B} :
    Γ ⊢ A →
      Γ ⊢ [bi| A ∨ B]
| orR2 {Γ} {A B} :
    Γ ⊢ B →
      Γ ⊢ [bi| A ∨ B]
| orL {Γ : BunchWithHole P} {A B C : Typ P} :
    Γ A ⊢ C →
    Γ B ⊢ C →
      Γ [bi| A ∨ B] ⊢ C
| flsL {Γ : BunchWithHole P} {C} :
    Γ (prop fls) ⊢ C
end

scoped infix:35 " ⊢ " => SeqEntails

namespace SeqEntails

theorem exchangeC (Γ : BunchWithHole P) (Δ₁ Δ₂ : Bunch P)
  : Γ (Δ₂,ᵇ Δ₁) ⊢ C → Γ (Δ₁,ᵇ Δ₂) ⊢ C := by
  intro h
  apply equiv (.subbunch Γ <| .commaComm)
  exact h

theorem exchangeS (Γ : BunchWithHole P) (Δ₁ Δ₂ : Bunch P)
  : Γ (Δ₂;ᵇ Δ₁) ⊢ C → Γ (Δ₁;ᵇ Δ₂) ⊢ C := by
  intro h
  apply equiv (.subbunch Γ <| .semiComm)
  exact h

theorem id {A : Typ P} : A ⊢ A := by
  rw [show (prop A = BunchWithHole.hole _) from rfl]
  induction A
  case atom =>
    exact id_atom
  case arr A B ih1 ih2 =>
    apply arrR
    suffices BunchWithHole.hole (prop _;ᵇ _) ⊢ _ from this
    apply exchangeS
    apply arrL
    · exact ih1
    apply exchangeS
    apply weaken
    exact ih2
  case tr =>
    apply trL
    apply trR
  case fls =>
    apply flsL
  case and A B ih1 ih2 =>
    apply andL
    apply andR
    · apply weaken
      exact ih1
    · apply exchangeS
      apply weaken
      exact ih2
  case or A B ih1 ih2 =>
    apply orL
    · exact orR1 ih1
    · exact orR2 ih2
  case dandy A B ih1 ih2 =>
    apply dandyR
    suffices BunchWithHole.hole (prop _,ᵇ _) ⊢ _ from this
    apply exchangeC
    apply dandyL ih1 ih2
  case emp =>
    apply empL
    apply empR
  case star A B ih1 ih2 =>
    apply starL
    apply starR ih1 ih2

def cut {Γ : BunchWithHole P} {Δ : Bunch P} {A C : Typ P}
        (D : Δ ⊢ A) (E : Γ A ⊢ C) : Γ Δ ⊢ C
  := by
  generalize hΓA : Γ A = ΓA at E
  cases hE : E
  case id_atom A' =>
    simp at hΓA
    rcases hΓA with ⟨rfl,rfl⟩
    exact D
  case equiv Δ₁ Γ' E₁ =>
    sorry
  case weaken Δ₁ Δ₂ Γ' E₁ =>
    have := BunchWithHole.eq_inv hΓA
    simp at this
    rcases this with (⟨Δ',h1,rfl⟩|⟨Δ',h1,Δ'',h2,h3⟩)
    case inr =>
      rw [← h2, ← h3]
      apply weaken
      rw [h3]
      rw [← h1, h3] at E₁
      apply cut D E₁
    case inl =>
      rw [eq_comm, BunchWithHole.eq_semi] at h1
      simp at h1
      rcases h1 with (⟨Γ'',rfl,rfl⟩|⟨Γ'',rfl,rfl⟩)
      · simp [BunchWithHole.comp_def]
        apply weaken
        rw [← BunchWithHole.comp_def] at E₁ ⊢
        apply cut D E₁
      · simp [BunchWithHole.comp_def]
        apply weaken
        apply E₁
  case contract Δ' Γ' E₁ =>
    sorry
  case empR => exfalso; simp at hΓA
  case empL Γ' E1 =>
    have := BunchWithHole.eq_inv hΓA
    rcases this with (h|h|⟨Δ',Δ'',h1,h2,h3⟩)
    case inr.inr =>
      rw [← h2, ← h3]
      apply empL
      rw [h3]
      have E' : Δ'' cunit A ⊢ C := by rw [← h3, h1]; exact E1
      apply cut D E'
    case inl | inr.inl =>
      clear hE hΓA E
      simp at h
      rcases h with ⟨_,⟨rfl,rfl⟩,rfl⟩
      simp_all
      cases D
      repeat sorry
  repeat sorry
termination_by cut Γ Δ A C D E => 0
decreasing_by sorry
