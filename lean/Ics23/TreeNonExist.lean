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

/-- **BST gap (root case).** In a sorted node, no member sits strictly between
the left subtree's max key and the right subtree's min key. This is the core
ordered-tree fact behind non-existence: adjacent leaves have no member between. -/
theorem root_gap_no_member (ih : HashOp) (pre mid suf : Bytes) (l r : MTree)
    (hs : SortedTree (.node ih pre mid suf l r))
    (key' value' : Bytes) (hm : TreeMember key' value' (.node ih pre mid suf l r))
    (h1 : bytesLt (maxKey l) key' = true) (h2 : bytesLt key' (minKey r) = true) : False := by
  obtain ⟨hsl, hsr, _⟩ := hs
  simp only [TreeMember] at hm
  rcases hm with hml | hmr
  · rcases member_le_maxKey l key' value' hsl hml with h | h
    · rw [h] at h1; simp [bytesLt_irrefl] at h1
    · have := bytesLt_trans _ _ _ h1 h; simp [bytesLt_irrefl] at this
  · rcases minKey_le_member r key' value' hsr hmr with h | h
    · rw [← h] at h2; simp [bytesLt_irrefl] at h2
    · have := bytesLt_trans _ _ _ h2 h; simp [bytesLt_irrefl] at this

/-- `ensure_inner`'s lower prefix bound. -/
theorem ensureInner_minle (op : InnerOp) (s : ProofSpec) (h : ensureInner op s = true) :
    s.innerSpec.minPrefixLength ≤ (op.prefixBytes.length : Int) := by
  unfold ensureInner at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2

/-- An all-right path (`ensure_right_most`: each step has empty suffix) reaches the
rightmost leaf — the proof's key is `maxKey t`, up to a collision. -/
theorem reaches_max (H : HashFn) (s : ProofSpec) (b : UInt8) (cs : Nat)
    (hH : FixedHash H cs)
    (hihash : s.innerSpec.hash = s.leafSpec.hash)
    (hlpre : s.leafSpec.prefixBytes = [b])
    (hmin : 1 ≤ s.innerSpec.minPrefixLength)
    (hLInj : ∀ k₁ v₁ k₂ v₂ r, applyLeaf H s.leafSpec k₁ v₁ = some r →
      applyLeaf H s.leafSpec k₂ v₂ = some r → (k₁ = k₂ ∧ v₁ = v₂) ∨ HashCollision H) :
    ∀ (t : MTree) (key value lh : Bytes) (path : List InnerOp) (root : Bytes),
      WFTree s b t →
      applyLeaf H s.leafSpec key value = some lh →
      (∀ op ∈ path, ensureInner op s = true ∧ op.suffix = []) →
      rootHash H t = some root →
      applyPath H s.innerSpec lh path = some root →
      (key = maxKey t ∧ TreeMember key value t) ∨ HashCollision H := by
  intro t
  induction t with
  | leaf top tk tv =>
    intro key value lh path root hwf hlh hpath hrh hap
    simp only [WFTree] at hwf; subst hwf
    rw [rootHash] at hrh
    cases path with
    | nil =>
      simp only [applyPath, Option.some.injEq] at hap; subst hap
      rcases hLInj key value tk tv _ hlh hrh with ⟨hk, hv⟩ | hc
      · exact Or.inl ⟨hk, hk.symm, hv.symm⟩
      · exact Or.inr hc
    | cons op rest =>
      have hii : IsInnerImage H s root :=
        applyPath_result_isInnerImage H s (op :: rest) lh root (by simp)
          (fun o ho => (hpath o ho).1) hap
      exact Or.inr (leafHash_innerImage_collision H s s.leafSpec tk tv root b
        hihash.symm hlpre hmin (ensureLeaf_self s.leafSpec) hrh hii)
  | node ih pre mid suf l r _ ihr =>
    intro key value lh path root hwf hlh hpath hrh hap
    obtain ⟨hih, hmid, hsuf, _, hprene, hprehead, _, hwfr⟩ := hwf
    subst hmid; subst hsuf; subst hih
    rw [rootHash] at hrh
    cases hl : rootHash H l with
    | none => rw [hl] at hrh; simp at hrh
    | some lhL =>
    cases hr : rootHash H r with
    | none => rw [hl, hr] at hrh; simp at hrh
    | some rhR =>
    rw [hl, hr] at hrh
    simp only [List.append_nil, Option.some.injEq] at hrh
    rcases List.eq_nil_or_concat path with hpnil | ⟨q, topOp, hpc⟩
    · subst hpnil
      simp only [applyPath, Option.some.injEq] at hap
      obtain ⟨tail, hlheq⟩ := applyLeaf_head H s.leafSpec key value lh b hlpre hlh
      rw [← hihash] at hlheq
      refine Or.inr (leaf_inner_domain_collision H s.innerSpec.hash (b :: tail)
        (pre ++ lhL ++ rhR) b (by simp) ?_ ?_)
      · cases hpc2 : pre with
        | nil => exact absurd hpc2 hprene
        | cons x xs =>
          rw [hpc2] at hprehead; simp only [List.cons_append, List.head?_cons] at hprehead ⊢
          exact hprehead
      · rw [← hlheq, hap]; exact hrh.symm
    · rw [List.concat_eq_append] at hpc; subst hpc
      obtain ⟨m, hpm, htop, _⟩ := (applyPath_snoc H s.innerSpec q topOp lh root).mp hap
      have htopimg := applyInner_image H topOp m root htop
      rw [ensureInner_hash topOp s (hpath topOp (by simp)).1] at htopimg
      by_cases hpe : topOp.prefixBytes ++ m ++ topOp.suffix = pre ++ lhL ++ rhR
      · have hmlen : m.length = cs :=
          applyPath_len H s.innerSpec cs hH q lh m
            (applyLeaf_len H cs hH s.leafSpec key value lh hlh) hpm
        have hmr : m = rhR := split_right pre lhL rhR topOp.prefixBytes m topOp.suffix cs
          hpe (rootHash_len H cs hH l lhL hl) (rootHash_len H cs hH r rhR hr) hmlen
          (by rw [(hpath topOp (by simp)).2]; rfl)
        rw [hmr] at hpm
        rcases ihr key value lh q rhR hwfr hlh
          (fun o ho => hpath o (List.mem_append.mpr (Or.inl ho))) hr hpm with ⟨hk, hmem⟩ | hcol
        · exact Or.inl ⟨by rw [hk]; rfl, Or.inr hmem⟩
        · exact Or.inr hcol
      · exact Or.inr (hashCollision_of H s.innerSpec.hash _ _ hpe (htopimg.trans hrh.symm))

/-- An all-left path (`ensure_left_most`: each step has a full `cs`-suffix) reaches
the leftmost leaf — the proof's key is `minKey t`, up to a collision. -/
theorem reaches_min (H : HashFn) (s : ProofSpec) (b : UInt8) (cs : Nat)
    (hH : FixedHash H cs)
    (hihash : s.innerSpec.hash = s.leafSpec.hash)
    (hlpre : s.leafSpec.prefixBytes = [b])
    (hmin : 1 ≤ s.innerSpec.minPrefixLength)
    (hLInj : ∀ k₁ v₁ k₂ v₂ r, applyLeaf H s.leafSpec k₁ v₁ = some r →
      applyLeaf H s.leafSpec k₂ v₂ = some r → (k₁ = k₂ ∧ v₁ = v₂) ∨ HashCollision H) :
    ∀ (t : MTree) (key value lh : Bytes) (path : List InnerOp) (root : Bytes),
      WFTree s b t →
      applyLeaf H s.leafSpec key value = some lh →
      (∀ op ∈ path, ensureInner op s = true ∧ op.suffix.length = cs) →
      rootHash H t = some root →
      applyPath H s.innerSpec lh path = some root →
      (key = minKey t ∧ TreeMember key value t) ∨ HashCollision H := by
  intro t
  induction t with
  | leaf top tk tv =>
    intro key value lh path root hwf hlh hpath hrh hap
    simp only [WFTree] at hwf; subst hwf
    rw [rootHash] at hrh
    cases path with
    | nil =>
      simp only [applyPath, Option.some.injEq] at hap; subst hap
      rcases hLInj key value tk tv _ hlh hrh with ⟨hk, hv⟩ | hc
      · exact Or.inl ⟨hk, hk.symm, hv.symm⟩
      · exact Or.inr hc
    | cons op rest =>
      have hii : IsInnerImage H s root :=
        applyPath_result_isInnerImage H s (op :: rest) lh root (by simp)
          (fun o ho => (hpath o ho).1) hap
      exact Or.inr (leafHash_innerImage_collision H s s.leafSpec tk tv root b
        hihash.symm hlpre hmin (ensureLeaf_self s.leafSpec) hrh hii)
  | node ih pre mid suf l r ihl _ =>
    intro key value lh path root hwf hlh hpath hrh hap
    obtain ⟨hih, hmid, hsuf, hppre, hprene, hprehead, hwfl, _⟩ := hwf
    subst hmid; subst hsuf; subst hih
    rw [rootHash] at hrh
    cases hl : rootHash H l with
    | none => rw [hl] at hrh; simp at hrh
    | some lhL =>
    cases hr : rootHash H r with
    | none => rw [hl, hr] at hrh; simp at hrh
    | some rhR =>
    rw [hl, hr] at hrh
    simp only [List.append_nil, Option.some.injEq] at hrh
    rcases List.eq_nil_or_concat path with hpnil | ⟨q, topOp, hpc⟩
    · subst hpnil
      simp only [applyPath, Option.some.injEq] at hap
      obtain ⟨tail, hlheq⟩ := applyLeaf_head H s.leafSpec key value lh b hlpre hlh
      rw [← hihash] at hlheq
      refine Or.inr (leaf_inner_domain_collision H s.innerSpec.hash (b :: tail)
        (pre ++ lhL ++ rhR) b (by simp) ?_ ?_)
      · cases hpc2 : pre with
        | nil => exact absurd hpc2 hprene
        | cons x xs =>
          rw [hpc2] at hprehead; simp only [List.cons_append, List.head?_cons] at hprehead ⊢
          exact hprehead
      · rw [← hlheq, hap]; exact hrh.symm
    · rw [List.concat_eq_append] at hpc; subst hpc
      obtain ⟨m, hpm, htop, _⟩ := (applyPath_snoc H s.innerSpec q topOp lh root).mp hap
      have htopimg := applyInner_image H topOp m root htop
      rw [ensureInner_hash topOp s (hpath topOp (by simp)).1] at htopimg
      by_cases hpe : topOp.prefixBytes ++ m ++ topOp.suffix = pre ++ lhL ++ rhR
      · have hmlen : m.length = cs :=
          applyPath_len H s.innerSpec cs hH q lh m
            (applyLeaf_len H cs hH s.leafSpec key value lh hlh) hpm
        have hlow : pre.length ≤ topOp.prefixBytes.length := by
          have := ensureInner_minle topOp s (hpath topOp (by simp)).1
          omega
        have hml : m = lhL := split_left pre lhL rhR topOp.prefixBytes m topOp.suffix cs
          hpe hlow (rootHash_len H cs hH l lhL hl) (rootHash_len H cs hH r rhR hr) hmlen
          (hpath topOp (by simp)).2
        rw [hml] at hpm
        rcases ihl key value lh q lhL hwfl hlh
          (fun o ho => hpath o (List.mem_append.mpr (Or.inl ho))) hl hpm with ⟨hk, hmem⟩ | hcol
        · exact Or.inl ⟨by rw [hk]; rfl, Or.inl hmem⟩
        · exact Or.inr hcol
      · exact Or.inr (hashCollision_of H s.innerSpec.hash _ _ hpe (htopimg.trans hrh.symm))

end Ics23
