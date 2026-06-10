/-
The verifier model, run end to end with a concrete SHA-256.

This grounds the abstract model: roots are computed with real hashing and
forgeries are rejected by computation (`native_decide`). It is the seed of the
Phase 2a differential oracle — the same `concreteHash` can drive the model
against the Rust/Go implementations over shared test vectors.
-/
import Ics23.Verify
import Ics23.Specs
import Ics23.Sha256

namespace Ics23

/-- A concrete `HashFn` covering the ops the shipped specs use (`noHash`,
`sha256`). Other ops are placeholders — not exercised by IAVL/Tendermint/SMT. -/
def concreteHash : HashFn := fun op data =>
  match op with
  | .sha256 => Sha256.hash data
  | _ => data

/-! ## End-to-end: a single-leaf IAVL proof -/

def demoLeafProof : ExistenceProof :=
  { key := [0x01], value := [0x02], leaf := iavlSpec.leafSpec, path := [] }

/-- The root computed by the model with real SHA-256. -/
def demoLeafRoot : Bytes := (calculateExistenceRoot concreteHash iavlSpec demoLeafProof).getD []

/-- The honest proof verifies. -/
example : verifyExistence concreteHash demoLeafProof iavlSpec demoLeafRoot [0x01] [0x02] = true := by
  native_decide

/-- A different value under the same root is rejected (the hash chain no longer
matches) — a value-swap forgery, refuted by computation. -/
def demoLeafForgery : ExistenceProof := { demoLeafProof with value := [0x03] }

example : verifyExistence concreteHash demoLeafForgery iavlSpec demoLeafRoot [0x01] [0x03] = false := by
  native_decide

/-! ## End-to-end: an IAVL proof with one inner step -/

def demoInner : InnerOp := { hash := .sha256, prefixBytes := [0x01, 0x02, 0x03, 0x04], suffix := [] }

def demoPathProof : ExistenceProof := { demoLeafProof with path := [demoInner] }

def demoPathRoot : Bytes := (calculateExistenceRoot concreteHash iavlSpec demoPathProof).getD []

/-- The honest two-level proof verifies. -/
example : verifyExistence concreteHash demoPathProof iavlSpec demoPathRoot [0x01] [0x02] = true := by
  native_decide

/-- The single-leaf root does not validate the two-level proof (and vice versa):
distinct tree shapes give distinct roots. -/
example : verifyExistence concreteHash demoPathProof iavlSpec demoLeafRoot [0x01] [0x02] = false := by
  native_decide

end Ics23
