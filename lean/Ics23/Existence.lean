/-
Existence binding (Theorem A), developed incrementally.

This file proves binding for the *same-shape* case: two existence proofs that
share the same leaf op and path ops, binding one key to two different values
under one root, yield a hash collision. It is parameterized by injectivity of
the leaf's length encoding (`hLeafInj`) and instantiated for both shipped leaf
shapes:

* `existence_binding_sameshape_noPrefix` — SMT/JMT (`NoPrefix` length).
* `existence_binding_sameshape_varProto` — IAVL / Tendermint (`VarProto` length).

The full chain is exercised: root extraction → path-fold injectivity
(`applyPath_sameops_inj`) → leaf-image cancellation → leaf-encoding injectivity
(`doLength_*_inj`). No `sorry` is used. The remaining gap to the *general*
`existence_binding` (in `Soundness.lean`) is the differing-path-structure case.
-/
import Ics23.Soundness
import Ics23.Varint

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

/-- `calculateExistenceRoot` factored into its leaf and path stages. -/
theorem calculateExistenceRoot_eq (H : HashFn) (s : ProofSpec) (p : ExistenceProof)
    (lh : Bytes) (hk : p.key.isEmpty = false) (hv : p.value.isEmpty = false)
    (hl : applyLeaf H p.leaf p.key p.value = some lh) :
    calculateExistenceRoot H s p = applyPath H s.innerSpec lh p.path := by
  simp [calculateExistenceRoot, hk, hv, hl]

/-- `doLength .noPrefix` is injective. -/
theorem doLength_noPrefix_inj (a b : Bytes)
    (h : doLength .noPrefix a = doLength .noPrefix b) : a = b := by
  simp only [doLength, Option.some.injEq] at h; exact h

/-- Leaf-value injectivity up to a collision: if two values encode to the same
leaf-value field under an injective length op, they are equal or their prehash
collides. -/
theorem prepareLeafData_inj (H : HashFn) (pre : HashOp) (L : LengthOp) (v₁ v₂ : Bytes)
    (hinj : ∀ a b, doLength L a = doLength L b → a = b)
    (h : prepareLeafData H pre L v₁ = prepareLeafData H pre L v₂)
    (hne1 : v₁.isEmpty = false) (hne2 : v₂.isEmpty = false) :
    v₁ = v₂ ∨ HashCollision H := by
  unfold prepareLeafData at h
  rw [if_neg (by simp [hne1]), if_neg (by simp [hne2])] at h
  have h' := hinj _ _ h
  by_cases hv : v₁ = v₂
  · exact Or.inl hv
  · exact Or.inr (hashCollision_of H pre v₁ v₂ hv h')

/-- **Theorem A, same-shape case (general length op).** Two existence proofs
sharing the same leaf op and path ops, binding the same (nonempty) key to two
different (nonempty) values under one root, yield a hash collision — provided the
leaf's length encoding is injective. -/
theorem existence_binding_sameshape
    (H : HashFn) (s : ProofSpec) (root key v₁ v₂ : Bytes)
    (p₁ p₂ : ExistenceProof)
    (hleafEq : p₁.leaf = p₂.leaf)
    (hpathEq : p₁.path = p₂.path)
    (hLeafInj : ∀ a b, doLength p₁.leaf.length a = doLength p₁.leaf.length b → a = b)
    (hk1 : p₁.key = key) (hk2 : p₂.key = key)
    (hkne : key.isEmpty = false)
    (hv1ne : v₁.isEmpty = false) (hv2ne : v₂.isEmpty = false)
    (hvv1 : p₁.value = v₁) (hvv2 : p₂.value = v₂)
    (hv : v₁ ≠ v₂)
    (h₁ : verifyExistence H p₁ s root key v₁ = true)
    (h₂ : verifyExistence H p₂ s root key v₂ = true) :
    HashCollision H := by
  have r1 := verifyExistence_root H p₁ s root key v₁ h₁
  have r2 := verifyExistence_root H p₂ s root key v₂ h₂
  have hk1e : p₁.key.isEmpty = false := by rw [hk1]; exact hkne
  have hk2e : p₂.key.isEmpty = false := by rw [hk2]; exact hkne
  have hv1e : p₁.value.isEmpty = false := by rw [hvv1]; exact hv1ne
  have hv2e : p₂.value.isEmpty = false := by rw [hvv2]; exact hv2ne
  cases hl1 : applyLeaf H p₁.leaf p₁.key p₁.value with
  | none => simp [calculateExistenceRoot, hk1e, hv1e, hl1] at r1
  | some lh₁ =>
  cases hl2 : applyLeaf H p₂.leaf p₂.key p₂.value with
  | none => simp [calculateExistenceRoot, hk2e, hv2e, hl2] at r2
  | some lh₂ =>
  have e1 : applyPath H s.innerSpec lh₁ p₁.path = some root := by
    rw [← calculateExistenceRoot_eq H s p₁ lh₁ hk1e hv1e hl1]; exact r1
  have e2 : applyPath H s.innerSpec lh₂ p₂.path = some root := by
    rw [← calculateExistenceRoot_eq H s p₂ lh₂ hk2e hv2e hl2]; exact r2
  rw [hpathEq] at e1
  rcases applyPath_sameops_inj H s.innerSpec p₂.path lh₁ lh₂ root e1 e2 with hlh | hc
  · rw [hk1, hvv1] at hl1
    rw [hk2, hvv2, ← hleafEq] at hl2
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
    by_cases himg :
        p₁.leaf.prefixBytes ++ pk ++ pv1 = p₁.leaf.prefixBytes ++ pk ++ pv2
    · have hpveq : pv1 = pv2 := List.append_cancel_left himg
      have hpv : prepareLeafData H p₁.leaf.prehashValue p₁.leaf.length v₁
               = prepareLeafData H p₁.leaf.prehashValue p₁.leaf.length v₂ := by
        rw [hpv1, hpv2, hpveq]
      rcases prepareLeafData_inj H p₁.leaf.prehashValue p₁.leaf.length v₁ v₂
          hLeafInj hpv hv1ne hv2ne with hveq | hcol
      · exact absurd hveq hv
      · exact hcol
    · exact hashCollision_of H p₁.leaf.hash _ _ himg (by rw [hl1, hl2]; exact hlh)
  · exact hc

/-- **Theorem A, SMT/JMT same-shape** (`NoPrefix` length). -/
theorem existence_binding_sameshape_noPrefix
    (H : HashFn) (s : ProofSpec) (root key v₁ v₂ : Bytes)
    (p₁ p₂ : ExistenceProof)
    (hleafEq : p₁.leaf = p₂.leaf) (hpathEq : p₁.path = p₂.path)
    (hLen : p₁.leaf.length = .noPrefix)
    (hk1 : p₁.key = key) (hk2 : p₂.key = key)
    (hkne : key.isEmpty = false)
    (hv1ne : v₁.isEmpty = false) (hv2ne : v₂.isEmpty = false)
    (hvv1 : p₁.value = v₁) (hvv2 : p₂.value = v₂) (hv : v₁ ≠ v₂)
    (h₁ : verifyExistence H p₁ s root key v₁ = true)
    (h₂ : verifyExistence H p₂ s root key v₂ = true) :
    HashCollision H :=
  existence_binding_sameshape H s root key v₁ v₂ p₁ p₂ hleafEq hpathEq
    (fun a b h => by rw [hLen] at h; exact doLength_noPrefix_inj a b h)
    hk1 hk2 hkne hv1ne hv2ne hvv1 hvv2 hv h₁ h₂

/-- **Theorem A, IAVL / Tendermint same-shape** (`VarProto` length). -/
theorem existence_binding_sameshape_varProto
    (H : HashFn) (s : ProofSpec) (root key v₁ v₂ : Bytes)
    (p₁ p₂ : ExistenceProof)
    (hleafEq : p₁.leaf = p₂.leaf) (hpathEq : p₁.path = p₂.path)
    (hLen : p₁.leaf.length = .varProto)
    (hk1 : p₁.key = key) (hk2 : p₂.key = key)
    (hkne : key.isEmpty = false)
    (hv1ne : v₁.isEmpty = false) (hv2ne : v₂.isEmpty = false)
    (hvv1 : p₁.value = v₁) (hvv2 : p₂.value = v₂) (hv : v₁ ≠ v₂)
    (h₁ : verifyExistence H p₁ s root key v₁ = true)
    (h₂ : verifyExistence H p₂ s root key v₂ = true) :
    HashCollision H :=
  existence_binding_sameshape H s root key v₁ v₂ p₁ p₂ hleafEq hpathEq
    (fun a b h => by rw [hLen] at h; exact doLength_varProto_inj a b h)
    hk1 hk2 hkne hv1ne hv2ne hvv1 hvv2 hv h₁ h₂

end Ics23
