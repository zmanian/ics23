/-
Existence binding (Theorem A), developed incrementally.

This file lands a fully-proved special case — binding for `NoPrefix`-length
specs (the SMT/JMT shape), with the two proofs sharing tree shape (same leaf op,
same path ops). This is the common value-swap forgery. It avoids the varint
self-delimiting argument that the length-prefixed (IAVL/Tendermint) case needs,
and exercises the full chain: root extraction → path-fold injectivity
(`applyPath_sameops_inj`) → leaf-image cancellation → leaf-encoding injectivity.

No `sorry` is used here.
-/
import Ics23.Soundness

namespace Ics23

/-- A successful `verifyExistence` pins the computed root. -/
theorem verifyExistence_root (H : HashFn) (p : ExistenceProof) (s : ProofSpec)
    (root key value : Bytes) (h : verifyExistence H p s root key value = true) :
    calculateExistenceRoot H s p = some root := by
  unfold verifyExistence at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, _⟩, hr⟩ := h
  cases hc : calculateExistenceRoot H s p with
  | none => rw [hc] at hr; simp at hr
  | some r =>
    rw [hc] at hr
    simp only [Option.some.injEq]
    exact (eq_of_beq hr)

/-- `calculateExistenceRoot` factored into its leaf and path stages, when the
key and value are nonempty and the leaf op succeeds. -/
theorem calculateExistenceRoot_eq (H : HashFn) (s : ProofSpec) (p : ExistenceProof)
    (lh : Bytes) (hk : p.key.isEmpty = false) (hv : p.value.isEmpty = false)
    (hl : applyLeaf H p.leaf p.key p.value = some lh) :
    calculateExistenceRoot H s p = applyPath H s.innerSpec lh p.path := by
  simp [calculateExistenceRoot, hk, hv, hl]

/-- Leaf injectivity for the `NoPrefix` length op: two `NoPrefix` leaf encodings
of the same prehash op agree iff the values agree — or the prehash collides. -/
theorem prepareLeafData_noPrefix_inj (H : HashFn) (pre : HashOp) (v₁ v₂ : Bytes)
    (h : prepareLeafData H pre .noPrefix v₁ = prepareLeafData H pre .noPrefix v₂)
    (hne1 : v₁.isEmpty = false) (hne2 : v₂.isEmpty = false) :
    v₁ = v₂ ∨ HashCollision H := by
  simp [prepareLeafData, doLength, hne1, hne2] at h
  -- h : H pre v₁ = H pre v₂
  by_cases hv : v₁ = v₂
  · exact Or.inl hv
  · exact Or.inr (hashCollision_of H pre v₁ v₂ hv h)

/-- **Theorem A, NoPrefix same-shape case.** For a spec whose leaf op uses
`NoPrefix` length, two existence proofs that share the same leaf op and path ops
and bind the same (nonempty) key to two different (nonempty) values under one
root yield a hash collision. -/
theorem existence_binding_noPrefix_sameshape
    (H : HashFn) (s : ProofSpec) (root key v₁ v₂ : Bytes)
    (p₁ p₂ : ExistenceProof)
    (hleafEq : p₁.leaf = p₂.leaf)
    (hpathEq : p₁.path = p₂.path)
    (hLenNoPrefix : p₁.leaf.length = .noPrefix)
    (hk1 : p₁.key = key) (hk2 : p₂.key = key)
    (hkne : key.isEmpty = false)
    (hv1ne : v₁.isEmpty = false) (hv2ne : v₂.isEmpty = false)
    (hvv1 : p₁.value = v₁) (hvv2 : p₂.value = v₂)
    (hv : v₁ ≠ v₂)
    (h₁ : verifyExistence H p₁ s root key v₁ = true)
    (h₂ : verifyExistence H p₂ s root key v₂ = true) :
    HashCollision H := by
  -- Roots both equal `root`.
  have r1 := verifyExistence_root H p₁ s root key v₁ h₁
  have r2 := verifyExistence_root H p₂ s root key v₂ h₂
  have hk1e : p₁.key.isEmpty = false := by rw [hk1]; exact hkne
  have hk2e : p₂.key.isEmpty = false := by rw [hk2]; exact hkne
  have hv1e : p₁.value.isEmpty = false := by rw [hvv1]; exact hv1ne
  have hv2e : p₂.value.isEmpty = false := by rw [hvv2]; exact hv2ne
  -- Leaf hashes exist (the roots are `some`).
  cases hl1 : applyLeaf H p₁.leaf p₁.key p₁.value with
  | none => simp [calculateExistenceRoot, hk1e, hv1e, hl1] at r1
  | some lh₁ =>
  cases hl2 : applyLeaf H p₂.leaf p₂.key p₂.value with
  | none => simp [calculateExistenceRoot, hk2e, hv2e, hl2] at r2
  | some lh₂ =>
  -- Rewrite the roots into the path-fold stage.
  have e1 : applyPath H s.innerSpec lh₁ p₁.path = some root := by
    rw [← calculateExistenceRoot_eq H s p₁ lh₁ hk1e hv1e hl1]; exact r1
  have e2 : applyPath H s.innerSpec lh₂ p₂.path = some root := by
    rw [← calculateExistenceRoot_eq H s p₂ lh₂ hk2e hv2e hl2]; exact r2
  -- Same path ops ⇒ equal leaf hashes (or a collision).
  rw [hpathEq] at e1
  rcases applyPath_sameops_inj H s.innerSpec p₂.path lh₁ lh₂ root e1 e2 with hlh | hc
  · -- lh₁ = lh₂ : equal leaf images.
    rw [hk1, hvv1] at hl1
    rw [hk2, hvv2, ← hleafEq] at hl2
    -- hl1 : applyLeaf H p₁.leaf key v₁ = some lh₁
    -- hl2 : applyLeaf H p₁.leaf key v₂ = some lh₂
    unfold applyLeaf at hl1 hl2
    cases hpk : prepareLeafData H p₁.leaf.prehashKey p₁.leaf.length key with
    | none => simp [hpk] at hl1
    | some pk =>
    cases hpv1 : prepareLeafData H p₁.leaf.prehashValue p₁.leaf.length v₁ with
    | none => simp [hpk, hpv1] at hl1
    | some pv1 =>
    cases hpv2 : prepareLeafData H p₁.leaf.prehashValue p₁.leaf.length v₂ with
    | none => simp [hpk, hpv2] at hl2
    | some pv2 =>
    simp only [hpk, hpv1, Option.some.injEq] at hl1
    simp only [hpk, hpv2, Option.some.injEq] at hl2
    -- hl1 : H leaf.hash (prefix ++ pk ++ pv1) = lh₁,  hl2 : ... pv2 = lh₂
    by_cases himg :
        p₁.leaf.prefixBytes ++ pk ++ pv1 = p₁.leaf.prefixBytes ++ pk ++ pv2
    · -- equal images ⇒ pv1 = pv2 ⇒ value encodings agree
      have hpveq : pv1 = pv2 := List.append_cancel_left himg
      rw [hLenNoPrefix] at hpv1 hpv2
      have hpv : prepareLeafData H p₁.leaf.prehashValue .noPrefix v₁
               = prepareLeafData H p₁.leaf.prehashValue .noPrefix v₂ := by
        rw [hpv1, hpv2, hpveq]
      rcases prepareLeafData_noPrefix_inj H p₁.leaf.prehashValue v₁ v₂ hpv hv1ne hv2ne
        with hveq | hcol
      · exact absurd hveq hv
      · exact hcol
    · -- differing images under the same leaf hash ⇒ collision
      exact hashCollision_of H p₁.leaf.hash _ _ himg (by rw [hl1, hl2]; exact hlh)
  · exact hc

end Ics23
