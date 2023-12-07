import BunchImpl.Bunch

namespace BunchImpl

open Bunch

/-- `Subbunch B b` iff `b` is a subtree of `B` -/
inductive Subbunch {P : Sort u} : Bunch P → Bunch P → Prop
| refl : Subbunch b b
| commaL : Subbunch BL b → Subbunch (BL,ᵇ BR) b
| commaR : Subbunch BR b → Subbunch (BL,ᵇ BR) b
| semiL : Subbunch BL b → Subbunch (BL;ᵇ BR) b
| semiR : Subbunch BR b → Subbunch (BL;ᵇ BR) b

namespace Subbunch

attribute [refl] refl
attribute [simp] refl commaL commaR semiL semiR

theorem comma_inv :
  Subbunch (BL,ᵇ BR) b ↔
    Subbunch BL b ∨ Subbunch BR b ∨ b = (BL,ᵇ BR) := by
  constructor
  · intro h; cases h <;> simp_all
  · intro h; cases h <;> aesop

theorem semi_inv :
  Subbunch (BL;ᵇ BR) b ↔
    Subbunch BL b ∨ Subbunch BR b ∨ b = (BL;ᵇ BR) := by
  constructor
  · intro h; cases h <;> simp_all
  · intro h; cases h <;> aesop

theorem trans : Subbunch b1 b2 → Subbunch b2 b3 → Subbunch b1 b3 := by
  intro h1 h2
  induction h1 <;> cases h2 <;> simp_all

theorem size_lt {B1 : Bunch P} : Subbunch B1 b1 → sizeOf B1 ≥ sizeOf b1 := by
  intro h1
  induction h1 <;> simp <;> linarith

def decide (B b : Bunch P) : Decidable (Subbunch B b) :=
  if h : B = b then
    .isTrue (h ▸ refl)
  else
    match B with
    | .prop _ => .isFalse fun h => by cases h; apply h; rfl
    | .sunit  => .isFalse fun h => by cases h; apply h; rfl
    | .cunit  => .isFalse fun h => by cases h; apply h; rfl
    | .semi  B1 B2 =>
      match decide B1 b, decide B2 b with
      | .isTrue h, _ => .isTrue (semiL h)
      | _, .isTrue h => .isTrue (semiR h)
      | .isFalse h1, .isFalse h2 =>
          .isFalse fun h => by cases h <;> simp_all
    | .comma B1 B2 =>
      match decide B1 b, decide B2 b with
      | .isTrue h, _ => .isTrue (commaL h)
      | _, .isTrue h => .isTrue (commaR h)
      | .isFalse h1, .isFalse h2 =>
          .isFalse fun h => by cases h <;> simp_all

instance : Decidable (Subbunch B b) := decide B b

theorem subst_hole (Γ : BunchWithHole P)
  : Subbunch (Γ b) b := by
  induction Γ <;> simp [*]

end Subbunch

def Nat.strongInduction {motive : Nat → Sort u}
      (h : ∀n, (∀ k, k < n → motive k) → motive n)
  : ∀ n, motive n :=
  fun n => h n (aux n)
where aux (n k) (hk : k < n) : motive k :=
  match n with
  | .zero =>
    h _ fun _ _ => by contradiction
  | .succ n =>
    if hn : k = n then
      hn ▸ h _ (aux n)
    else
      have : k < n := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ hk) hn
      aux n _ this

@[elab_as_elim]
def Bunch.subbunch_induction {motive : Bunch P → Prop}
      (h : ∀ B, (∀ b, Subbunch B b → B ≠ b → motive b) → motive B)
  : ∀ B, motive B :=
  fun B => h B (aux B)
where aux (B b) (hsub : Subbunch B b) (hne : B ≠ b) : motive b := by {
  cases B
  case prop | sunit | cunit =>
    exfalso; cases hsub; contradiction
  case semi B1 B2 =>
    cases hsub
    case refl => contradiction
    case semiL hsub =>
      if hb : B1 = b then
        rw [← hb]; apply h _ (aux B1)
      else
        exact aux B1 _ hsub hb
    case semiR hsub =>
      if hb : B2 = b then
        rw [← hb]; apply h _ (aux B2)
      else
        exact aux B2 _ hsub hb
  case comma B1 B2 =>
    cases hsub
    case refl => contradiction
    case commaL hsub =>
      if hb : B1 = b then
        rw [← hb]; apply h _ (aux B1)
      else
        exact aux B1 _ hsub hb
    case commaR hsub =>
      if hb : B2 = b then
        rw [← hb]; apply h _ (aux B2)
      else
        exact aux B2 _ hsub hb
}
