/-
Ordered-tree position semantics — the foundation for non-existence soundness
(Theorem B). A path determines a leaf's position via the branch each inner op
takes (`order_from_padding`). This file begins connecting the path-structure
checks (`ensure_left_most` / `ensure_right_most`) to those positions.

Scoped first to specs with **no empty children** (`empty_child = []`), which
covers IAVL and Tendermint; there the placeholder logic never fires, so the
checks reduce cleanly to "every step is the leftmost / rightmost branch".
-/
import Ics23.NonExist
import Ics23.Verify

namespace Ics23

/-- Lexicographic order on leaf positions (root→leaf branch sequences),
shorter-is-less — the order in which leaves appear left-to-right. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a == b then lexLt as bs else false

/-- A successful `byteRange` returns a slice of exactly the requested length. -/
theorem byteRange_length (data : Bytes) (start len : Nat) (s : Bytes)
    (h : byteRange data start len = some s) : s.length = len := by
  unfold byteRange at h
  by_cases hb : start + len ≤ data.length
  · rw [if_pos hb] at h
    injection h with hs
    rw [← hs, List.length_take, List.length_drop]
    omega
  · rw [if_neg hb] at h; exact absurd h (by simp)

/-- With no empty children and positive child size, a step is never a (left)
empty placeholder. -/
theorem leftBranchesAreEmpty_false_of_noEmpty (isp : InnerSpec) (op : InnerOp)
    (hempty : isp.emptyChild = []) (hcs : isp.childSize > 0) :
    leftBranchesAreEmpty isp op = false := by
  unfold leftBranchesAreEmpty
  cases h : orderFromPadding isp op with
  | none => rfl
  | some idx =>
    by_cases h0 : idx = 0
    · simp [h0]
    · simp only [h0, if_false]
      by_cases hlen : op.prefixBytes.length < idx * isp.childSize.toNat
      · simp [hlen]
      · simp only [hlen, if_false]
        have hcsn : 0 < isp.childSize.toNat := by omega
        rw [List.all_eq_false]
        refine ⟨0, by simp only [List.mem_range]; omega, ?_⟩
        simp only [hempty]
        cases hbr : byteRange op.prefixBytes
            (op.prefixBytes.length - idx * isp.childSize.toNat + 0 * isp.childSize.toNat)
            isp.childSize.toNat with
        | none => decide
        | some s =>
          have hsl := byteRange_length _ _ _ _ hbr
          simp only [beq_iff_eq, Option.some.injEq]
          intro hse
          rw [hse, List.length_nil] at hsl
          omega

/-- The leaf position a path encodes: the branch each inner op takes, root→leaf.
`none` if any step's branch is undetermined. -/
def pathPosition (isp : InnerSpec) (path : List InnerOp) : Option (List Nat) :=
  path.reverse.mapM (orderFromPadding isp)

/-- The store key-sortedness invariant (finding F4): any two existence proofs to
`root` agree on order — left-to-right *position* order matches key order. This is
the hypothesis ICS23 requires ("stores must be lexicographically ordered") and
that `verify_non_existence` does **not** itself enforce. -/
def KeySorted (H : HashFn) (s : ProofSpec) (root : Bytes) : Prop :=
  ∀ (ep₁ ep₂ : ExistenceProof) (pos₁ pos₂ : List Nat),
    verifyExistence H ep₁ s root ep₁.key ep₁.value = true →
    verifyExistence H ep₂ s root ep₂.key ep₂.value = true →
    pathPosition s.innerSpec ep₁.path = some pos₁ →
    pathPosition s.innerSpec ep₂.path = some pos₂ →
    (lexLt pos₁ pos₂ = true ↔
      bytesLt (keyForComparison H s ep₁.key) (keyForComparison H s ep₂.key) = true)

/-- If every element maps to `some 0`, `mapM` yields all zeros. -/
theorem mapM_all_zero {α : Type} (l : List α) (f : α → Option Nat)
    (h : ∀ a ∈ l, f a = some 0) :
    l.mapM f = some (List.replicate l.length 0) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.mapM_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    rfl

/-- A step matching branch 0's padding sits at branch 0 (left child): branch 0 is
checked first by `order_from_padding`. -/
theorem orderFromPadding_zero (isp : InnerSpec) (op : InnerOp) (pad0 : Padding)
    (hn : 1 ≤ isp.childOrder.length)
    (hpad : getPadding isp 0 = some pad0) (h : hasPadding op pad0 = true) :
    orderFromPadding isp op = some 0 := by
  unfold orderFromPadding
  cases hlen : isp.childOrder.length with
  | zero => rw [hlen] at hn; omega
  | succ m =>
    rw [List.range_succ_eq_map, List.find?_cons]
    simp only [hpad, h]

/-- For a spec with no empty children, `ensure_left_most` forces every step to
match the left-branch (branch 0) padding — i.e. every step is a genuine left
child. The first ordered-tree-position fact. -/
theorem ensureLeftMost_allLeftPadding (isp : InnerSpec) (path : List InnerOp)
    (hempty : isp.emptyChild = []) (hcs : isp.childSize > 0)
    (h : ensureLeftMost isp path = true) :
    ∀ op ∈ path, ∃ pad, getPadding isp 0 = some pad ∧ hasPadding op pad = true := by
  unfold ensureLeftMost at h
  cases hpad : getPadding isp 0 with
  | none => rw [hpad] at h; exact absurd h (by simp)
  | some pad =>
    rw [hpad] at h
    intro op hop
    have hstep := (List.all_eq_true.mp h) op hop
    rw [leftBranchesAreEmpty_false_of_noEmpty isp op hempty hcs, Bool.or_false] at hstep
    exact ⟨pad, rfl, hstep⟩

/-- A left-most path's position is all-zeros (the leftmost leaf), for a spec with
no empty children. The first concrete position computed from a path check. -/
theorem ensureLeftMost_position (isp : InnerSpec) (path : List InnerOp)
    (hempty : isp.emptyChild = []) (hcs : isp.childSize > 0)
    (hn : 1 ≤ isp.childOrder.length)
    (h : ensureLeftMost isp path = true) :
    pathPosition isp path = some (List.replicate path.length 0) := by
  unfold pathPosition
  have hall : ∀ op ∈ path.reverse, orderFromPadding isp op = some 0 := by
    intro op hop
    rw [List.mem_reverse] at hop
    obtain ⟨pad, hpad, hhp⟩ := ensureLeftMost_allLeftPadding isp path hempty hcs h op hop
    exact orderFromPadding_zero isp op pad hn hpad hhp
  rw [mapM_all_zero path.reverse (orderFromPadding isp) hall, List.length_reverse]

/-- Symmetric fact: with no empty children, a step is never a (right) empty
placeholder. -/
theorem rightBranchesAreEmpty_false_of_noEmpty (isp : InnerSpec) (op : InnerOp)
    (hempty : isp.emptyChild = []) (hcs : isp.childSize > 0) :
    rightBranchesAreEmpty isp op = false := by
  unfold rightBranchesAreEmpty
  cases h : orderFromPadding isp op with
  | none => rfl
  | some idx =>
    by_cases h0 : isp.childOrder.length - 1 - idx = 0
    · simp [h0]
    · simp only [h0, if_false]
      by_cases hsuf : op.suffix.length ≠ isp.childSize.toNat
      · simp [hsuf]
      · simp only [hsuf, if_false] at *
        have hcsn : 0 < isp.childSize.toNat := by omega
        rw [List.all_eq_false]
        refine ⟨0, by simp only [List.mem_range]; omega, ?_⟩
        simp only [hempty]
        cases hbr : byteRange op.suffix (0 * isp.childSize.toNat) isp.childSize.toNat with
        | none => decide
        | some s =>
          have hsl := byteRange_length _ _ _ _ hbr
          simp only [beq_iff_eq, Option.some.injEq]
          intro hse
          rw [hse, List.length_nil] at hsl
          omega

/-- `ensure_right_most` analogue: every step matches the right-branch padding. -/
theorem ensureRightMost_allRightPadding (isp : InnerSpec) (path : List InnerOp)
    (hempty : isp.emptyChild = []) (hcs : isp.childSize > 0)
    (h : ensureRightMost isp path = true) :
    ∀ op ∈ path, ∃ pad, getPadding isp (isp.childOrder.length - 1) = some pad ∧
      hasPadding op pad = true := by
  unfold ensureRightMost at h
  cases hpad : getPadding isp (isp.childOrder.length - 1) with
  | none => rw [hpad] at h; exact absurd h (by simp)
  | some pad =>
    rw [hpad] at h
    intro op hop
    have hstep := (List.all_eq_true.mp h) op hop
    rw [rightBranchesAreEmpty_false_of_noEmpty isp op hempty hcs, Bool.or_false] at hstep
    exact ⟨pad, rfl, hstep⟩

end Ics23

