/-
Soundness scaffolding for the existence verifier.

This file contains:
  * `HashCollision` — the constructive target of every soundness theorem.
  * `WellFormed` — the decidable side condition on a `ProofSpec` under which
    the verifier is sound (Theorem C certifies the shipped specs satisfy it).
  * supporting lemmas that are fully proved.
  * Theorem A (`existence_binding`) — stated precisely, proof in progress.

Theorem A is the headline soundness property. Its proof is staged: the
structural lemmas it rests on are being landed first; the top-level statement is
recorded now (with `sorry`) so the target is fixed and reviewable. No `sorry`
is relied upon by `WellFormed`, the spec certificates, or the proved lemmas.
-/
import Ics23.Verify
import Ics23.Specs

namespace Ics23

/-! ## The collision target -/

/-- A concrete collision in the hash family `H`: two distinct preimages under
the same `HashOp` with the same image. Every soundness theorem concludes by
exhibiting one of these, so the results are unconditional (no hash assumptions). -/
def HashCollision (H : HashFn) : Prop :=
  ∃ (op : HashOp) (a b : Bytes), a ≠ b ∧ H op a = H op b

/-! ## Well-formedness of a `ProofSpec`

These are the side conditions Theorems A and B assume. They are phrased as a
decidable `Bool` predicate so the shipped specs can be certified by computation. -/

/-- A length op whose output length is determined by the encoding itself
(length-prefixed) or fixed by construction (`Require*`). `noPrefix` is the only
non-determining op. -/
def lengthDetermining : LengthOp → Bool
  | .noPrefix => false
  | _ => true

/-- The fixed output length of a hash op, or `none` for `noHash` (identity,
hence variable length). -/
def fixedOutputLen : HashOp → Option Nat
  | .noHash => none
  | .sha256 => some 32
  | .sha512 => some 64
  | .keccak256 => some 32
  | .ripemd160 => some 20
  | .bitcoin => some 20
  | .sha512256 => some 32
  | .blake2b512 => some 64
  | .blake2s256 => some 32
  | .blake3 => some 32

/-- The leaf encoding `prefix ++ enc(prehashKey key) ++ enc(prehashValue value)`
parses unambiguously into its two fields: either the `LengthOp` delimits them, or
both prehash images have fixed length. This is the heart of leaf injectivity. -/
def leafDelimitingB (leaf : LeafOp) : Bool :=
  lengthDetermining leaf.length
  || ((fixedOutputLen leaf.prehashKey).isSome && (fixedOutputLen leaf.prehashValue).isSome)

/-- `l` is a permutation of `[0, …, l.length - 1]`. Decidable, and sufficient
because every index in range appearing in a list of that length forces a perm. -/
def isPermRange (l : List Nat) : Bool :=
  (List.range l.length).all (fun i => l.contains i)

/-- Inner-spec well-formedness: positive child size, sensible prefix window,
the `max < min + childSize` invariant (the same one `ensure_inner` enforces per
op), at least a binary node, a valid child ordering, and an `emptyChild` that is
either absent or exactly `childSize` bytes. -/
def innerWFB (isp : InnerSpec) : Bool :=
  (isp.childSize > 0)
  && (isp.minPrefixLength ≥ 0)
  && (isp.maxPrefixLength ≥ isp.minPrefixLength)
  && (isp.maxPrefixLength < isp.minPrefixLength + isp.childSize)
  && (isp.childOrder.length ≥ 2)
  && isPermRange isp.childOrder
  && (isp.emptyChild.isEmpty || ((isp.emptyChild.length : Int) = isp.childSize))

/-- The full decidable well-formedness predicate. The nonempty leaf prefix is
what makes leaf/inner domain separation (the `!has_prefix(leafPrefix, ...)`
check in `ensure_inner`) meaningful. -/
def wellFormedB (s : ProofSpec) : Bool :=
  leafDelimitingB s.leafSpec
  && (s.leafSpec.prefixBytes.length > 0)
  && innerWFB s.innerSpec

/-- A spec is well-formed when it passes the decidable check. -/
def WellFormed (s : ProofSpec) : Prop := wellFormedB s = true

instance (s : ProofSpec) : Decidable (WellFormed s) := by
  unfold WellFormed; infer_instance

/-! ## Theorem C: the shipped specs are well-formed

These hold by computation. They are the standalone, immediately-useful artifact:
a machine-checked answer to "is this `ProofSpec` safe to accept?". -/

theorem iavl_wellFormed : WellFormed iavlSpec := by decide

theorem tendermint_wellFormed : WellFormed tendermintSpec := by decide

theorem smt_wellFormed : WellFormed smtSpec := by decide

/-! ## Supporting lemmas (fully proved) -/

/-- An inner op's preimage is injective in its child: same op, same surrounding
prefix/suffix, so equal images force equal children. This is the cancellation
step used when walking two proofs up to a shared node. -/
theorem innerImage_inj (op : InnerOp) (c₁ c₂ : Bytes) :
    op.prefixBytes ++ c₁ ++ op.suffix = op.prefixBytes ++ c₂ ++ op.suffix ↔ c₁ = c₂ := by
  constructor
  · intro h
    have h2 : op.prefixBytes ++ c₁ = op.prefixBytes ++ c₂ := List.append_cancel_right h
    exact List.append_cancel_left h2
  · intro h; rw [h]

/-- `hasPrefix` is reflexive: every byte string is a prefix of itself. -/
theorem hasPrefix_refl (b : Bytes) : hasPrefix b b = true := by
  unfold hasPrefix
  simp

/-! ## Theorem A: existence binding (soundness)

A single root cannot bind one key to two different values without a hash
collision. Equivalently: if a forger produces two existence proofs for the same
key with different values that both verify against the same root and a
well-formed spec, that forger has found a hash collision.

Proof strategy (being landed incrementally):
  1. From `verifyExistence` true, both proofs share the same leaf spec, so the
     leaf hash op and the leaf encoding shape agree.
  2. `leafDelimitingB` ⇒ the leaf encoding is injective in `(key, value)`, so
     different values give different leaf preimages — unless the prehash images
     already collide, which *is* a collision.
  3. Both paths fold up to the same `root`. Induct down the two paths using
     `innerImage_inj` and leaf/inner domain separation (`ensure_inner`'s
     `!has_prefix`): at the first divergence the images coincide but the
     preimages differ, yielding the collision. -/
theorem existence_binding
    (H : HashFn) (hNoHash : ∀ b, H .noHash b = b)
    (s : ProofSpec) (hwf : WellFormed s)
    (root key v₁ v₂ : Bytes)
    (p₁ p₂ : ExistenceProof)
    (hv : v₁ ≠ v₂)
    (h₁ : verifyExistence H p₁ s root key v₁ = true)
    (h₂ : verifyExistence H p₂ s root key v₂ = true) :
    HashCollision H := by
  sorry

end Ics23
