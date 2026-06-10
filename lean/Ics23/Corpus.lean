/-
Regression corpus: concrete inputs encoded as machine-checked acceptance/
rejection facts. These pin the spec-level invariants from
`docs/verification/properties.md` and double as the model's own test suite.

Everything here is decided by computation (no hash function required), so each
`example` is a proof, not a test that might silently stop running.
-/
import Ics23.Verify
import Ics23.NonExist
import Ics23.Specs
import Ics23.Soundness

namespace Ics23

/-! ## Positive controls -/

/-- A leaf-only proof whose leaf matches the IAVL leaf spec passes spec checks. -/
def iavlLeafProof : ExistenceProof :=
  { key := [1], value := [2], leaf := iavlSpec.leafSpec, path := [] }

example : checkExistenceSpec iavlLeafProof iavlSpec = true := by decide

/-- A well-formed Tendermint inner op is accepted by `ensureInner`. -/
def tmValidInner : InnerOp := { hash := .sha256, prefixBytes := [1], suffix := [] }

example : ensureInner tmValidInner tendermintSpec = true := by decide

/-! ## A2 — leaf/inner domain separation

An inner op whose prefix begins with the leaf prefix must be rejected, else a
leaf hash could be reinterpreted as an inner hash (depth confusion). -/
def tmLeafPrefixInner : InnerOp := { hash := .sha256, prefixBytes := [0, 9], suffix := [] }

example : ensureInner tmLeafPrefixInner tendermintSpec = false := by decide

/-! ## A3 — positional unambiguity -/

/-- Suffix length not a multiple of `child_size` is rejected. -/
def tmBadSuffixInner : InnerOp := { hash := .sha256, prefixBytes := [1], suffix := [0] }

example : ensureInner tmBadSuffixInner tendermintSpec = false := by decide

/-- Inner prefix shorter than `min_prefix_length` is rejected. -/
def tmShortPrefixInner : InnerOp := { hash := .sha256, prefixBytes := [], suffix := [] }

example : ensureInner tmShortPrefixInner tendermintSpec = false := by decide

/-! ## C — malformed specs are not well-formed -/

/-- Non-positive `child_size`. -/
def negChildSizeSpec : ProofSpec :=
  { tendermintSpec with
    innerSpec := { tendermintSpec.innerSpec with childSize := 0 } }

example : wellFormedB negChildSizeSpec = false := by decide

/-- A1-split shape: `NoPrefix` length with variable-length prehash on both
fields — the `key ++ value` boundary is ambiguous, so the spec is unsafe. -/
def splitSpec : ProofSpec :=
  { tendermintSpec with
    leafSpec := { tendermintSpec.leafSpec with
                  length := .noPrefix, prehashValue := .noHash } }

example : wellFormedB splitSpec = false := by decide

/-! ## Depth bounds -/

/-- With `min_depth ≠ 0`, a path shorter than `min_depth` is rejected. -/
def depthBoundedSpec : ProofSpec := { iavlSpec with minDepth := 2, maxDepth := 4 }

def shallowProof : ExistenceProof :=
  { key := [1], value := [2], leaf := iavlSpec.leafSpec, path := [] }

example : checkExistenceSpec shallowProof depthBoundedSpec = false := by decide

/-! ## Non-existence: padding, ordering, and empty-branch placeholders

These exercise the SMT inner spec (binary, `child_size = 32`, 32-byte zero
`empty_child`) — the logic where Dragonberry-class bugs live. Mirrors the Rust
`check_empty_branch` test. `native_decide` is used for the 32-byte cases. -/

/-- Left child position: prefix length 1, 32-byte right sibling in the suffix. -/
def smtLeftStep : InnerOp :=
  { hash := .sha256, prefixBytes := [7], suffix := List.replicate 32 0 }

/-- Right child position: 32-byte left sibling in the prefix, empty suffix. -/
def smtRightStep : InnerOp :=
  { hash := .sha256, prefixBytes := List.replicate 32 0 ++ [7], suffix := [] }

example : orderFromPadding smtSpec.innerSpec smtLeftStep = some 0 := by native_decide
example : orderFromPadding smtSpec.innerSpec smtRightStep = some 1 := by native_decide

/-- The left child is immediately left of the right child. -/
example : isLeftStep smtSpec.innerSpec smtLeftStep smtRightStep = true := by native_decide

/-- A genuine left child is left-most. -/
example : ensureLeftMost smtSpec.innerSpec [smtLeftStep] = true := by native_decide

/-- A genuine right child is right-most. -/
example : ensureRightMost smtSpec.innerSpec [smtRightStep] = true := by native_decide

/-- A placeholder at branch 1 whose left sibling is the empty child is a valid
left-most step (the left subtree is empty). -/
def smtLeftPlaceholder : InnerOp :=
  { hash := .sha256, prefixBytes := [9] ++ List.replicate 32 0, suffix := [] }

example : leftBranchesAreEmpty smtSpec.innerSpec smtLeftPlaceholder = true := by native_decide
example : ensureLeftMost smtSpec.innerSpec [smtLeftPlaceholder] = true := by native_decide

/-- A branch-1 step whose left sibling is *not* the empty child is not a valid
left-most placeholder. -/
def smtNotLeftmost : InnerOp :=
  { hash := .sha256, prefixBytes := [9] ++ List.replicate 31 0 ++ [5], suffix := [] }

example : leftBranchesAreEmpty smtSpec.innerSpec smtNotLeftmost = false := by native_decide
example : ensureLeftMost smtSpec.innerSpec [smtNotLeftmost] = false := by native_decide

end Ics23
