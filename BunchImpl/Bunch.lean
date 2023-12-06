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
deriving Inhabited

namespace Bunch

scoped infixr:40 " ,ᵇ " => Bunch.comma
scoped infixr:40 " ;ᵇ " => Bunch.semi
instance : Coe (Typ P) (Bunch P) := ⟨prop⟩

end Bunch

open Bunch

inductive BunchWithHole (P : Sort u)
| hole
| commaL (l : BunchWithHole P) (r : Bunch P)
| commaR (l : Bunch P) (r : BunchWithHole P)
| semiL (l : BunchWithHole P) (r : Bunch P)
| semiR (l : Bunch P) (r : BunchWithHole P)

namespace BunchWithHole

def subst (b : Bunch P) : BunchWithHole P → Bunch P
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

instance : FunLike (BunchWithHole P) (Bunch P) (fun _ => Bunch P) where
  coe hole b := subst b hole
  coe_injective' := by
    intro a b h
    sorry

def id : BunchWithHole P := hole

@[simp] theorem id_def : id b = b := by
  simp [id, subst, FunLike.coe]

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

@[simp] theorem idem (Γ : BunchWithHole P) (b : Bunch P) : Γ b = b ↔ Γ = id := by
  induction Γ <;> simp [FunLike.coe, subst, id] <;> (
    intro h; have := congrArg sizeOf h
    simp at this
    zify at this
    sorry
  )

@[simp] theorem eq_prop (Γ : BunchWithHole P) : Γ b = prop φ ↔ Γ = id ∧ b = .prop φ := by
  cases Γ <;> simp [FunLike.coe, subst, id]

end BunchWithHole
