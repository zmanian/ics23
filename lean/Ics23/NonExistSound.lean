/-
Non-existence soundness (Theorem B), staged.

States Theorem B precisely and proves supporting facts about the lexicographic
byte ordering `bytesLt` that the neighbor checks rely on. The main proof needs
the ordered-tree semantics an `InnerSpec` describes and is landed separately;
the statement is recorded here so the target is fixed (mirroring how Theorem A
was staged). Only `nonexistence_sound` uses `sorry`.
-/
import Ics23.NonExist
import Ics23.Soundness

namespace Ics23

/-- `bytesLt` is irreflexive: no byte string is strictly less than itself. -/
theorem bytesLt_irrefl (a : Bytes) : bytesLt a a = false := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    show (if x < x then true else if x == x then bytesLt xs xs else false) = false
    rw [if_neg (UInt8.lt_irrefl x), if_pos (by simp)]
    exact ih

/-- A strictly-ordered key cannot also be equal: `bytesLt` excludes equality. -/
theorem bytesLt_ne (a b : Bytes) (h : bytesLt a b = true) : a ≠ b := by
  intro hab
  rw [hab, bytesLt_irrefl] at h
  exact Bool.noConfusion h

/-- **Theorem B (non-existence soundness), statement.** A non-existence proof
for `key` and an existence proof for `key` cannot both verify under the same
spec and root without a hash collision.

Proof obligation (see `docs/verification/properties.md`): formalize the ordered
tree an `InnerSpec` describes — `ensure_left_most`, `ensure_right_most`, and
`ensure_left_neighbor` pin the absent key strictly between two adjacent leaves —
then show an existence proof placing `key` between those neighbors contradicts
the strict ordering, forcing a collision. Respects
`prehash_key_before_comparison` (the order is over hashed keys for SMT/JMT). -/
theorem nonexistence_sound
    (H : HashFn) (hNoHash : ∀ b, H .noHash b = b)
    (s : ProofSpec) (hwf : WellFormed s)
    (root key value : Bytes)
    (nep : NonExistenceProof) (ep : ExistenceProof)
    (hkey : ep.key = key)
    (hne : verifyNonExistence H nep s root key = true)
    (hex : verifyExistence H ep s root key value = true) :
    HashCollision H := by
  sorry

end Ics23
