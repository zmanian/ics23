/-
Honest-root Merkle tree model (Option 1).

The byte-level theorems (`existence_binding_shaped`, etc.) conclude a disjunction
with ambiguity arms (findings F3/F5) because, against an *arbitrary* root, the
verifier accepts inner ops whose prefix/child/suffix are adversarial bytes that
merely hash correctly. In deployment the root is the hash of a tree some honest
full node actually built (the adversary controls the proof, not the root's
provenance). This file models that: an inductive ordered Merkle tree with a
`rootHash`, against which accepted proofs follow *genuine* structure.

The payoff: both F3 "readings" of a node correspond to real left/right children,
so `membership_sound` (accepted existence proof ⇒ genuine membership, up to a
collision) holds with no ambiguity arm — which strengthens Theorem A and is the
engine for Theorem B.

Binary trees (all shipped specs are binary). A node's hash mirrors how the
verifier's inner ops combine: `H ih (pre ++ leftHash ++ mid ++ rightHash ++ suf)`,
so a left-child op `{ih, pre, mid++rh++suf}` and a right-child op
`{ih, pre++lh++mid, suf}` both reconstruct it.
-/
import Ics23.Verify
import Ics23.Soundness

namespace Ics23

/-- A binary Merkle tree with explicit structural bytes at each node. -/
inductive MTree where
  | leaf : LeafOp → Bytes → Bytes → MTree
  | node : HashOp → Bytes → Bytes → Bytes → MTree → MTree → MTree
  deriving Inhabited

/-- The root hash of a tree, mirroring the verifier's leaf/inner hashing. -/
def rootHash (H : HashFn) : MTree → Option Bytes
  | .leaf op k v => applyLeaf H op k v
  | .node ih pre mid suf l r =>
    match rootHash H l, rootHash H r with
    | some lh, some rh => some (H ih (pre ++ lh ++ mid ++ rh ++ suf))
    | _, _ => none

/-- `(key, value)` is a leaf of the tree. -/
def TreeMember (key val : Bytes) : MTree → Prop
  | .leaf _ k v => k = key ∧ v = val
  | .node _ _ _ _ l r => TreeMember key val l ∨ TreeMember key val r

/-- The left-child inner op for a node: child is the left subtree's hash. -/
def leftChildOp (ih : HashOp) (pre mid suf rh : Bytes) : InnerOp :=
  { hash := ih, prefixBytes := pre, suffix := mid ++ rh ++ suf }

/-- The right-child inner op for a node: the left sibling sits in the prefix. -/
def rightChildOp (ih : HashOp) (pre mid suf lh : Bytes) : InnerOp :=
  { hash := ih, prefixBytes := pre ++ lh ++ mid, suffix := suf }

/-- A left-child op applied to the (nonempty) left subtree hash reproduces the
node hash. -/
theorem leftChildOp_apply (H : HashFn) (ih : HashOp) (pre mid suf lh rh : Bytes)
    (hlh : lh.isEmpty = false) :
    applyInner H (leftChildOp ih pre mid suf rh) lh
      = some (H ih (pre ++ lh ++ mid ++ rh ++ suf)) := by
  unfold applyInner leftChildOp
  rw [if_neg (by rw [hlh]; simp)]
  simp [List.append_assoc]

/-- A right-child op applied to the (nonempty) right subtree hash reproduces the
node hash. -/
theorem rightChildOp_apply (H : HashFn) (ih : HashOp) (pre mid suf lh rh : Bytes)
    (hrh : rh.isEmpty = false) :
    applyInner H (rightChildOp ih pre mid suf lh) rh
      = some (H ih (pre ++ lh ++ mid ++ rh ++ suf)) := by
  unfold applyInner rightChildOp
  rw [if_neg (by rw [hrh]; simp)]

/-- **Membership soundness (Theorem A, honest-root form).** If `root` is the hash
of a real tree `t` and an existence proof for `(key, value)` verifies against
`root`, then `(key, value)` is genuinely in `t` — or the proof exhibits a hash
collision. No ambiguity arm: against a real root, the F3 readings are genuine
left/right children. -/
theorem membership_sound (H : HashFn) (s : ProofSpec) :
    ∀ (t : MTree) (ep : ExistenceProof) (root key value : Bytes),
      rootHash H t = some root →
      verifyExistence H ep s root key value = true →
      TreeMember key value t ∨ HashCollision H := by
  sorry

end Ics23
