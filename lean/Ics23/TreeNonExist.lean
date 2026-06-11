/-
Non-existence soundness (Theorem B) via the honest-root tree model.

`membership_sound` (Tree.lean) already gives that a non-existence proof's
bracketing neighbors — and any claimed key — are *genuine* members of the real
tree. What remains is the ordered-tree (BST) reasoning: in a key-sorted tree, no
member sits strictly between two position-adjacent leaves. This file builds that.

Key order is the raw byte order `bytesLt` (the Tendermint / `prehash_key_before_
comparison = false` case; the SMT case composes with the prehash and is analogous).
-/
import Ics23.Tree
import Ics23.NonExist
import Ics23.NonExistSound

namespace Ics23

/-- The rightmost leaf's key. -/
def maxKey : MTree → Bytes
  | .leaf _ k _ => k
  | .node _ _ _ _ _ r => maxKey r

/-- The leftmost leaf's key. -/
def minKey : MTree → Bytes
  | .leaf _ k _ => k
  | .node _ _ _ _ l _ => minKey l

/-- A key-sorted (BST) tree: at each node, the left subtree's max key is strictly
below the right subtree's min key, recursively. -/
def SortedTree : MTree → Prop
  | .leaf _ _ _ => True
  | .node _ _ _ _ l r => SortedTree l ∧ SortedTree r ∧ bytesLt (maxKey l) (minKey r) = true

/-- `min ≤ max` for any tree (with `≤` meaning `= ∨ bytesLt`). -/
theorem minKey_le_maxKey (t : MTree) (hs : SortedTree t) :
    minKey t = maxKey t ∨ bytesLt (minKey t) (maxKey t) = true := by
  induction t with
  | leaf _ k _ => exact Or.inl rfl
  | node _ _ _ _ l r ihl ihr =>
    obtain ⟨hsl, hsr, hlr⟩ := hs
    -- minKey node = minKey l, maxKey node = maxKey r
    have hl := ihl hsl   -- minKey l ≤ maxKey l
    have hr := ihr hsr   -- minKey r ≤ maxKey r
    refine Or.inr ?_
    -- minKey l ≤ maxKey l < minKey r ≤ maxKey r
    show bytesLt (minKey l) (maxKey r) = true
    have step1 : bytesLt (minKey l) (minKey r) = true := by
      rcases hl with h | h
      · rw [h]; exact hlr
      · exact bytesLt_trans _ _ _ h hlr
    rcases hr with h | h
    · rw [← h]; exact step1
    · exact bytesLt_trans _ _ _ step1 h

/-- A member's key is `≤` the tree's max key. -/
theorem member_le_maxKey (t : MTree) (key value : Bytes)
    (hs : SortedTree t) (hm : TreeMember key value t) :
    key = maxKey t ∨ bytesLt key (maxKey t) = true := by
  induction t with
  | leaf _ k _ =>
    simp only [TreeMember] at hm
    exact Or.inl hm.1.symm
  | node _ _ _ _ l r ihl ihr =>
    obtain ⟨hsl, hsr, hlr⟩ := hs
    simp only [TreeMember] at hm
    rcases hm with hml | hmr
    · -- in left: key ≤ maxKey l < minKey r ≤ maxKey r
      refine Or.inr ?_
      have hkl := ihl hsl hml
      have hrr := minKey_le_maxKey r hsr
      have hkr : bytesLt key (minKey r) = true := by
        rcases hkl with h | h
        · rw [h]; exact hlr
        · exact bytesLt_trans _ _ _ h hlr
      show bytesLt key (maxKey r) = true
      rcases hrr with h | h
      · rw [← h]; exact hkr
      · exact bytesLt_trans _ _ _ hkr h
    · exact ihr hsr hmr

/-- A member's key is `≥` the tree's min key. -/
theorem minKey_le_member (t : MTree) (key value : Bytes)
    (hs : SortedTree t) (hm : TreeMember key value t) :
    minKey t = key ∨ bytesLt (minKey t) key = true := by
  induction t with
  | leaf _ k _ =>
    simp only [TreeMember] at hm
    exact Or.inl hm.1
  | node _ _ _ _ l r ihl ihr =>
    obtain ⟨hsl, hsr, hlr⟩ := hs
    simp only [TreeMember] at hm
    rcases hm with hml | hmr
    · exact ihl hsl hml
    · -- in right: minKey l ≤ maxKey l < minKey r ≤ key
      refine Or.inr ?_
      have hkr := ihr hsr hmr
      have hll := minKey_le_maxKey l hsl
      have hlk : bytesLt (maxKey l) key = true := by
        rcases hkr with h | h
        · rw [← h]; exact hlr
        · exact bytesLt_trans _ _ _ hlr h
      show bytesLt (minKey l) key = true
      rcases hll with h | h
      · rw [h]; exact hlk
      · exact bytesLt_trans _ _ _ h hlk

end Ics23
