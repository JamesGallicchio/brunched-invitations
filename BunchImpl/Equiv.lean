import BunchImpl.Subbunch

namespace BunchImpl

open Bunch

/-- This is the relation on bunches
which we close over to get bunch equivalence. -/
inductive PreEquiv {P : Sort u} : Bunch P → Bunch P → Prop
/- Comm. monoid laws for `,` with `cunit` -/
| cunitL : PreEquiv (cunit,ᵇ b) b
| cunitR : PreEquiv (b,ᵇ cunit) b
| commaAssoc : PreEquiv (b1,ᵇ b2,ᵇ b3) ((b1,ᵇ b2),ᵇ b3)
| commaComm : PreEquiv (b1,ᵇ b2) (b2,ᵇ b1)
/- Comm. monoid laws for `;` with `sunit` -/
| sunitL : PreEquiv (sunit;ᵇ b) b
| sunitR : PreEquiv (b;ᵇ sunit) b
| semiAssoc : PreEquiv (b1;ᵇ b2;ᵇ b3) ((b1;ᵇ b2);ᵇ b3)
| semiComm : PreEquiv (b1;ᵇ b2) (b2;ᵇ b1)
/- Subtree congruence -/
| subbunch {h : BunchWithHole P} {b1 b2}
  : PreEquiv b1 b2 → PreEquiv (h b1) (h b2)

namespace PreEquiv

@[simp] theorem prop_left : ¬PreEquiv (prop A) B := by
  intro h
  generalize hA' : prop A = A' at h
  induction h <;> simp at hA'
  rcases hA' with ⟨rfl,rfl⟩
  simp at *

@[simp] theorem sunit_left : ¬PreEquiv sunit B := by
  intro h
  generalize hA' : sunit = A' at h
  induction h <;> simp at hA'
  rcases hA' with ⟨rfl,rfl⟩
  simp at *

@[simp] theorem cunit_left : ¬PreEquiv cunit B := by
  intro h
  generalize hA' : cunit = A' at h
  induction h <;> simp at hA'
  rcases hA' with ⟨rfl,rfl⟩
  simp at *

@[simp] theorem prop_right : PreEquiv B (prop A) ↔
    B = (cunit,ᵇ prop A) ∨
    B = (prop A,ᵇ cunit) ∨
    B = (sunit;ᵇ prop A) ∨
    B = (prop A;ᵇ sunit)
  := by
  constructor
  · intro h
    generalize hA' : prop A = A' at h
    induction h <;> simp_all
  · rintro (rfl|rfl|rfl|rfl)
    · exact cunitL
    · exact cunitR
    · exact sunitL
    · exact sunitR

@[simp] theorem sunit_right : PreEquiv B (sunit) ↔
    B = (cunit,ᵇ sunit) ∨
    B = (sunit,ᵇ cunit) ∨
    B = (sunit;ᵇ sunit) ∨
    B = (sunit;ᵇ sunit)
  := by
  constructor
  · intro h
    generalize hA' : sunit = A' at h
    induction h <;> simp_all
  · rintro (rfl|rfl|rfl|rfl)
    · exact cunitL
    · exact cunitR
    · exact sunitL
    · exact sunitR

@[simp] theorem cunit_right : PreEquiv B (cunit) ↔
    B = (cunit,ᵇ cunit) ∨
    B = (cunit,ᵇ cunit) ∨
    B = (sunit;ᵇ cunit) ∨
    B = (cunit;ᵇ sunit)
  := by
  constructor
  · intro h
    generalize hA' : cunit = A' at h
    induction h <;> simp_all
  · rintro (rfl|rfl|rfl|rfl)
    · exact cunitL
    · exact cunitR
    · exact sunitL
    · exact sunitR

end PreEquiv

/-- Equivalence on bunches. -/
def Equiv {P : Type u} : Bunch P → Bunch P → Prop :=
  EqvGen PreEquiv

namespace Equiv

/- This gives access to `≈` notation on bunches. -/
instance : HasEquiv (Bunch P) := ⟨Equiv⟩

def is_equivalence : Equivalence (@Equiv P) :=
  EqvGen.is_equivalence _

@[simp, refl] theorem refl {b : Bunch P} : b ≈ b := EqvGen.refl b

theorem trans {b1 b2 b3 : Bunch P} (h1 : b1 ≈ b2) (h2 : b2 ≈ b3) : b1 ≈ b3 :=
  EqvGen.trans _ _ _ h1 h2

theorem symm {b1 b2 : Bunch P} (h1 : b1 ≈ b2) : b2 ≈ b1 :=
  EqvGen.symm _ _ h1

theorem symm_iff (b1 b2 : Bunch P) : b1 ≈ b2 ↔ b2 ≈ b1 := ⟨symm,symm⟩

theorem cunitL     : (cunit,ᵇ b)   ≈ b               := EqvGen.rel _ _ <| .cunitL ..
theorem cunitR     : (b,ᵇ cunit)   ≈ b               := EqvGen.rel _ _ <| .cunitR ..
theorem commaAssoc : (b1,ᵇ b2,ᵇ b3) ≈ ((b1,ᵇ b2),ᵇ b3) := EqvGen.rel _ _ <| .commaAssoc ..
theorem commaComm  : (b1,ᵇ b2)     ≈ (b2,ᵇ b1)        := EqvGen.rel _ _ <| .commaComm ..
theorem sunitL     : (sunit;ᵇ b)   ≈ b               := EqvGen.rel _ _ <| .sunitL ..
theorem sunitR     : (b;ᵇ sunit)   ≈ b               := EqvGen.rel _ _ <| .sunitR ..
theorem semiAssoc  : (b1;ᵇ b2;ᵇ b3) ≈ ((b1;ᵇ b2);ᵇ b3) := EqvGen.rel _ _ <| .semiAssoc ..
theorem semiComm   : (b1;ᵇ b2)     ≈ (b2;ᵇ b1)        := EqvGen.rel _ _ <| .semiComm ..
theorem subbunch {b1 b2} (h : BunchWithHole P)
      : b1 ≈ b2 → (h b1) ≈ (h b2)
  := by
  intro e
  induction e with
  | rel _ _ h =>
    apply EqvGen.rel
    apply PreEquiv.subbunch
    exact h
  | refl =>
    exact refl
  | symm _ _ _ ih =>
    exact symm ih
  | trans _ _ _ _ _ ih1 ih2 =>
    exact trans ih1 ih2

theorem commaL {b1 b2 b3 : Bunch P} : b1 ≈ b2 → (b1,ᵇ b3) ≈ (b2,ᵇ b3) :=
  fun h => subbunch (.commaL .hole _) h

theorem commaR {b1 b2 b3 : Bunch P} : b1 ≈ b2 → (b3,ᵇ b1) ≈ (b3,ᵇ b2) :=
  fun h => subbunch (.commaR _ .hole) h

theorem semiL {b1 b2 b3 : Bunch P} : b1 ≈ b2 → (b1;ᵇ b3) ≈ (b2;ᵇ b3) :=
  fun h => subbunch (.semiL .hole _) h

theorem semiR {b1 b2 b3 : Bunch P} : b1 ≈ b2 → (b3;ᵇ b1) ≈ (b3;ᵇ b2) :=
  fun h => subbunch (.semiR _ .hole) h



theorem hole_prop_inv {Γ : BunchWithHole P} {A : Typ P} {Δ : Bunch P}
  : Γ A ≈ Δ → ∃ Γ' : BunchWithHole P, Δ = Γ' A := by
  intro e
  induction Δ
  case prop =>
    simp at e
    refine ⟨.hole,?_⟩; simp
  sorry

end Equiv
