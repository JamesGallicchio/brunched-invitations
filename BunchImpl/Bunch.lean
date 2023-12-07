import BunchImpl.Typ

namespace BunchImpl

open Typ

/-- Bunches, the contexts of bunched logic. -/
inductive Bunch (P : Sort u)
| prop : Typ P → Bunch P
| cunit : Bunch P
| comma : Bunch P → Bunch P → Bunch P
| sunit : Bunch P
| semi : Bunch P → Bunch P → Bunch P
deriving Inhabited, DecidableEq

namespace Bunch

scoped infixr:40 " ,ᵇ " => Bunch.comma
scoped infixr:40 " ;ᵇ " => Bunch.semi
instance : Coe (Typ P) (Bunch P) := ⟨prop⟩

@[simp] theorem neq_left_comma
  : (b1 ,ᵇ b2) ≠ b1 := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this
  linarith

@[simp] theorem neq_right_comma
  : (b1 ,ᵇ b2) ≠ b2 := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this

@[simp] theorem neq_self_left_comma
  : b1 ≠ (b1 ,ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this
  linarith

@[simp] theorem neq_self_right_comma
  : b2 ≠ (b1 ,ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this

@[simp] theorem neq_left_semi
  : (b1 ;ᵇ b2) ≠ b1 := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this
  linarith

@[simp] theorem neq_right_semi
  : (b1 ;ᵇ b2) ≠ b2 := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this

@[simp] theorem neq_self_left_semi
  : b1 ≠ (b1 ;ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this
  linarith

@[simp] theorem neq_self_right_semi
  : b2 ≠ (b1 ;ᵇ b2) := by
  intro h; have := congrArg sizeOf h; clear h
  simp at this

end Bunch

open Bunch

inductive BunchWithHole (P : Sort u)
| hole
| commaL (l : BunchWithHole P) (r : Bunch P)
| commaR (l : Bunch P) (r : BunchWithHole P)
| semiL (l : BunchWithHole P) (r : Bunch P)
| semiR (l : Bunch P) (r : BunchWithHole P)

namespace BunchWithHole

@[simp] def subst (b : Bunch P) : BunchWithHole P → Bunch P
| hole => b
| commaL l r => subst b l ,ᵇ r
| commaR l r => l ,ᵇ subst b r
| semiL  l r => subst b l ;ᵇ r
| semiR  l r => l ;ᵇ subst b r

theorem sizeOf_pos (h : BunchWithHole P) : sizeOf h > 0 := by
  induction h <;> simp

@[simp] theorem sizeOf_subst (b : Bunch P) (h) :
    sizeOf (subst b h) = sizeOf b + sizeOf h - 1 := by
  induction h <;> simp [subst, *] <;> sorry

@[simp] theorem subst_idem : subst b Γ = b ↔ Γ = hole := by
  constructor
  · intro h; have := sizeOf_subst b Γ
    rw [h] at this
    rw [Nat.add_sub_assoc (sizeOf_pos _)] at this
    simp at this
    cases Γ <;> simp at * <;> (
      revert this
      suffices ¬ _ ≥ _ from this
      simp
      rw [Nat.add_assoc]
      apply Nat.lt_add_of_pos_right
      first | (apply Nat.add_pos_left; apply sizeOf_pos)
            | (apply Nat.add_pos_right; apply sizeOf_pos)
    )
  · rintro rfl; simp

@[simp] theorem idem_subst : b = subst b Γ ↔ Γ = hole := by
  rw [show _ = _ ↔ _ = _ from ⟨Eq.symm, Eq.symm⟩]
  simp

instance : FunLike (BunchWithHole P) (Bunch P) (fun _ => Bunch P) where
  coe hole b := subst b hole
  coe_injective' := by
    intro Γ1 Γ2 h
    simp at h
    have : ∀ b, _ = _ := congrFun h
    clear h
    induction Γ1 generalizing Γ2 <;> simp_all <;> (
      cases Γ2 <;> simp at this ⊢
    )
    repeat sorry

@[simp] theorem hole_def : hole b = b := rfl
@[simp] theorem commaL_def : commaL l r b = (l b,ᵇ r) := rfl
@[simp] theorem commaR_def : commaR l r b = (l,ᵇ r b) := rfl
@[simp] theorem semiL_def  : semiL  l r b = (l b;ᵇ r) := rfl
@[simp] theorem semiR_def  : semiR  l r b = (l;ᵇ r b) := rfl

@[pp_dot] def comp (Γ₁ Γ₂ : BunchWithHole P) : BunchWithHole P :=
  match Γ₁ with
  | hole => Γ₂
  | commaL l r => commaL (comp l Γ₂) r
  | commaR l r => commaR l (comp r Γ₂)
  | semiL  l r => semiL  (comp l Γ₂) r
  | semiR  l r => semiR  l (comp r Γ₂)

theorem comp_def (h1 h2 : BunchWithHole P) (b : Bunch P)
  : (h1.comp h2) b = h1 (h2 b) := by
  induction h1 <;> simp_all [comp, FunLike.coe, subst]

@[simp] theorem idem (Γ : BunchWithHole P) (b : Bunch P)
    : Γ b = b ↔ Γ = hole := by
  induction Γ <;> simp [FunLike.coe, subst] <;> (
    intro h; have := congrArg sizeOf h
    simp at this
    zify at this
    sorry
  )

@[simp] theorem eq_prop (Γ : BunchWithHole P)
    : Γ b = prop φ ↔ Γ = hole ∧ b = .prop φ := by
  cases Γ <;> simp [FunLike.coe, subst]

@[simp] theorem prop_eq (Γ : BunchWithHole P)
    : prop φ = Γ b ↔ Γ = hole ∧ b = .prop φ := by
  rw [show (prop φ = _ ↔ _ = prop φ) from ⟨Eq.symm, Eq.symm⟩]
  simp

@[simp] theorem eq_cunit (Γ : BunchWithHole P)
    : Γ b = cunit ↔ Γ = hole ∧ b = cunit := by
  cases Γ <;> simp [FunLike.coe, subst]

@[simp] theorem cunit_eq (Γ : BunchWithHole P)
    : cunit = Γ b ↔ Γ = hole ∧ b = cunit := by
  rw [show (_ = _ ↔ _ = _) from ⟨Eq.symm, Eq.symm⟩]
  simp

@[simp] theorem eq_sunit (Γ : BunchWithHole P)
    : Γ b = sunit ↔ Γ = hole ∧ b = sunit := by
  cases Γ <;> simp [FunLike.coe, subst]

@[simp] theorem sunit_eq (Γ : BunchWithHole P)
    : sunit = Γ b ↔ Γ = hole ∧ b = sunit := by
  rw [show (_ = _ ↔ _ = _) from ⟨Eq.symm, Eq.symm⟩]
  simp

theorem eq_comma (Γ : BunchWithHole P)
    : Γ b = (Δ₁,ᵇ Δ₂) ↔
        Γ = hole ∧ b = (Δ₁,ᵇ Δ₂)
      ∨ ∃ Γ', Γ = .commaL Γ' Δ₂ ∧ Γ' b = Δ₁
      ∨ ∃ Γ', Γ = .commaR Δ₁ Γ' ∧ Γ' b = Δ₂
  := by
  cases Γ <;> aesop

theorem eq_semi (Γ : BunchWithHole P)
    : Γ b = (Δ₁;ᵇ Δ₂) ↔
        Γ = hole ∧ b = (Δ₁;ᵇ Δ₂)
      ∨ ∃ Γ', Γ = .semiL Γ' Δ₂ ∧ Γ' b = Δ₁
      ∨ ∃ Γ', Γ = .semiR Δ₁ Γ' ∧ Γ' b = Δ₂
  := by
  cases Γ <;> aesop

end BunchWithHole
