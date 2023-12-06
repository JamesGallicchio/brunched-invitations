import BunchImpl.Subbunch

namespace BunchImpl

open Bunch

/-- This is the relation on bunches
which we close over to get bunch equivalence. -/
inductive BunchPreEquiv {P : Sort u} : Bunch P → Bunch P → Prop
/- Comm. monoid laws for `,` with `cunit` -/
| cunitL : BunchPreEquiv (cunit,ᵇ b) b
| cunitR : BunchPreEquiv (b,ᵇ cunit) b
| commaAssoc : BunchPreEquiv (b1,ᵇ b2,ᵇ b3) ((b1,ᵇ b2),ᵇ b3)
| commaComm : BunchPreEquiv (b1,ᵇ b2) (b2,ᵇ b1)
/- Comm. monoid laws for `;` with `sunit` -/
| sunitL : BunchPreEquiv (sunit;ᵇ b) b
| sunitR : BunchPreEquiv (b;ᵇ sunit) b
| semiAssoc : BunchPreEquiv (b1;ᵇ b2;ᵇ b3) ((b1;ᵇ b2);ᵇ b3)
| semiComm : BunchPreEquiv (b1;ᵇ b2) (b2;ᵇ b1)
/- Subtree congruence -/
| subbunch (h : BunchWithHole P) (b1 b2)
  : BunchPreEquiv b1 b2 → BunchPreEquiv (h b1) (h b2)

/-- Equivalence on bunches. -/
def BunchEquiv {P : Type u} : Bunch P → Bunch P → Prop :=
  EqvGen BunchPreEquiv

def BunchEquiv.is_equivalence : Equivalence (@BunchEquiv P) :=
  EqvGen.is_equivalence _

/- This gives access to `≈` notation on bunches. -/
instance : HasEquiv (Bunch P) := ⟨BunchEquiv⟩

theorem BunchEquiv.ofPre {b1 b2 : Bunch P} (h1 : BunchPreEquiv b1 b2) : b1 ≈ b2 :=
  EqvGen.rel _ _ h1

theorem BunchEquiv.trans {b1 b2 b3 : Bunch P} (h1 : b1 ≈ b2) (h2 : b2 ≈ b3) : b1 ≈ b3 :=
  EqvGen.trans _ _ _ h1 h2

theorem BunchEquiv.symm {b1 b2 : Bunch P} (h1 : b1 ≈ b2) : b2 ≈ b1 :=
  EqvGen.symm _ _ h1

theorem BunchEquiv.subbunch (h : BunchWithHole P) (e : Γ ≈ Δ) : (h Γ ≈ h Δ) := by
  induction e with
  | rel _ _ h =>
    apply EqvGen.rel
    apply BunchPreEquiv.subbunch
    exact h
  | refl =>
    exact .refl _
  | symm _ _ _ ih =>
    exact .symm ih
  | trans _ _ _ _ _ ih1 ih2 =>
    exact .trans ih1 ih2
