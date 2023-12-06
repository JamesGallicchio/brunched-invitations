import Mathlib

namespace BunchImpl

/-! ## Propositions -/

/-- Propositions, with atoms in sort `P` -/
inductive Typ (P : Sort u)
| atom : P → Typ P
/- Structural connectives -/
| arr : Typ P → Typ P → Typ P
| tr : Typ P
| and : Typ P → Typ P → Typ P
| fls : Typ P
| or : Typ P → Typ P → Typ P
/- Linear connectives -/
| dandy : Typ P → Typ P → Typ P
| emp : Typ P
| star : Typ P → Typ P → Typ P
deriving Inhabited

namespace Typ

declare_syntax_cat bi_typ

syntax:50 bi_typ:51 " -* " bi_typ:50 : bi_typ
syntax:50 bi_typ:51 " → "  bi_typ:50 : bi_typ
syntax:60 bi_typ:61 " ∨ "  bi_typ:50 : bi_typ
syntax:70 bi_typ:71 " ∧ "  bi_typ:50 : bi_typ
syntax:70 bi_typ:71 " * "  bi_typ:50 : bi_typ
syntax term:71 : bi_typ

syntax "[bi| " bi_typ " ]" : term
macro_rules
| `([bi| $t:term ]) => `(show Typ _ from $t)
| `([bi| $t1 -* $t2 ]) => `(Typ.dandy [bi| $t1] [bi| $t2])
| `([bi| $t1 → $t2 ]) => `(Typ.arr [bi| $t1] [bi| $t2])
| `([bi| $t1 ∨ $t2 ]) => `(Typ.or [bi| $t1] [bi| $t2])
| `([bi| $t1 ∧ $t2 ]) => `(Typ.and [bi| $t1] [bi| $t2])
| `([bi| $t1 * $t2 ]) => `(Typ.star [bi| $t1] [bi| $t2])
