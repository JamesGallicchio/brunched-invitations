import BunchImpl.Term.Bunch

namespace BunchImpl

inductive Term.X (P : Sort u) (V : Sort v)
| fwd (var : V)
| sendEmp
| recvEmp (K : Term.X P V)
| sendStar (v1 : V) (v2 : V) (K : Term.X P V)
| recvStar (K : V → V → Term.X P V)

def Term (P) := ∀ V, Term.X P V
