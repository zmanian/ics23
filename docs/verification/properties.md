# ICS23 Verification — Property Catalogue (Phase 0)

Status: living document. Companion to `docs/rfc/001-formal-verification.md` and
the Lean development under `lean/`.

This catalogue enumerates the properties the formal model must establish and the
invariants the verifier relies on. Each property links to where it is enforced
in the code and where it lives in the Lean model. It also records the regression
corpus: concrete malicious inputs the model is required to reject.

## Sources to mine

- `docs/audits/ICS-23 - Zellic Audit Report.pdf` — extract each finding and its
  invariant; add any that are not already covered below. (Not yet transcribed
  into this document; do not treat the list below as incorporating it.)
- The 2020 Informal Systems audit of the original `confio/ics23`.
- The Cosmos "Dragonberry" advisory (Oct 2022) — proof-forgery class in the
  Cosmos proof-verification stack; the canonical motivation.
- The ICS-023 specification (vector commitments).

## Modeling assumptions (must stay honest)

These are the places where the Lean model deliberately differs from the Rust.
Each is justified as *sound* (the model accepts at least every proof the code
accepts), so a soundness theorem about the model transfers to the code.

1. **Optional fields collapsed.** `ProofSpec.{leaf,inner}_spec` and
   `ExistenceProof.leaf` are `Option` in proto/Rust; a `None` triggers an
   immediate reject. The model makes them non-optional, dropping inputs the
   code rejects. Enlarges the accepted set ⇒ sound to omit.
2. **IAVL prefix checks omitted.** `ensure_leaf_prefix` / `ensure_inner_prefix`
   (`rust/src/api.rs`) only fire when the spec equals the IAVL spec and can only
   reject. Omitting them enlarges the accepted set ⇒ sound to omit. (A later
   increment may add them to also reason about IAVL prefix structure.)
3. **Hash family abstract.** `do_hash` is modeled as an arbitrary
   `HashFn : HashOp → Bytes → Bytes` with the single law `noHash = id`. No
   collision-resistance assumption is made; soundness theorems *exhibit* a
   collision instead.
4. **Spec integers are `Int`.** Faithful to the `i32` proto fields, so malformed
   (e.g. negative) specs are representable and excluded by `WellFormed` rather
   than by Lean typing. (Wrap/overflow of the `i32`/`usize` casts in the Rust is
   a separate, code-level concern handled by Kani in Phase 3, not here.)

## Properties

### A. Existence binding (soundness) — headline

A well-formed spec and a fixed root cannot bind one key to two different values
without a hash collision.

- Enforced by: `verify_existence` + `check_existence_spec` +
  `calculate_existence_root_for_spec` (`rust/src/verify.rs`).
- Model: `Ics23.existence_binding` (statement landed; proof in progress).
- Rests on:
  - **A1 Leaf-encoding injectivity.** `prefix ++ enc(prehash key) ++ enc(prehash value)`
    parses uniquely into `(key, value)` — via a length-determining `LengthOp`
    (VarProto/Fixed*/Require*) or fixed-length prehash images on both fields.
    Captured by `leafDelimitingB`. Violated ⇒ a forger can re-split bytes into a
    different `(key, value)`.
  - **A2 Leaf/inner domain separation.** No accepted inner-op preimage carries
    the leaf prefix (`ensure_inner`: `!has_prefix(leaf_spec.prefix, inner.prefix)`).
    Requires a nonempty leaf prefix (`wellFormedB`). Violated ⇒ a leaf hash can
    be reinterpreted as an inner hash (depth confusion).
  - **A3 Positional unambiguity.** `min_prefix_length`, `max_prefix_length`,
    `child_size`, suffix length, and `max < min + child_size` together fix a
    child's position in its parent. Captured by `innerWFB` and `ensure_inner`.
  - **A4 Inner preimage injectivity in the child.** Same op ⇒ equal images force
    equal children. Proved: `Ics23.innerImage_inj`.

### B. Non-existence soundness

A well-formed spec and a fixed root cannot simultaneously admit a non-existence
proof for key `k` and an existence proof for `k`.

- Enforced by: `verify_non_existence`, `ensure_left_most`, `ensure_right_most`,
  `ensure_left_neighbor`, `left_branches_are_empty`, `right_branches_are_empty`
  (`rust/src/verify.rs`).
- Model: not yet (next increment). Requires formalizing the ordered-tree
  semantics an `InnerSpec` describes, arbitrary `child_order` permutations, and
  `empty_child` for sparse trees.
- Note: when `prehash_key_before_comparison` is set (SMT/JMT), the ordering is
  over hashed keys, so the guarantee is non-existence of the *hashed* key.

### C. Spec well-formedness certificate — proved

A decidable `WellFormed` predicate capturing exactly A1–A3's side conditions,
plus machine-checked certificates that the shipped specs satisfy it.

- Model: `wellFormedB` / `WellFormed`; certificates `iavl_wellFormed`,
  `tendermint_wellFormed`, `smt_wellFormed` (proved by `decide`).
- Standalone value: a checkable answer to "is this custom `ProofSpec` safe?"

### D. Implementation safety (Rust) — Phase 3 (Kani)

Panic freedom, no lossy/overflowing integer casts (notably the `i32`/`i64`/`usize`
casts in `ensure_inner`, `ensure_inner_prefix`, and compressed-batch index
handling), termination, input-bounded allocation. Not in the Lean model.

Landed (`rust/src/kani_proofs.rs`, `#[cfg(kani)]`, run by `cargo kani` / CI):
three harnesses **verified** by CBMC — the `ensure_inner` prefix-bound `i32`
arithmetic and the `get_padding` products are overflow-free under well-formed
bounds, and the `left_branches_are_empty` slice accesses are always in bounds
(the Dragonberry-class out-of-range-slice surface). Noted finding: an adversarial
spec with an enormous `child_size` could overflow the `i32` prefix-bound product;
the harnesses pin the safe precondition. Remaining: panic-freedom of the
`Result`-returning entry points (`do_length`, `proto_len`) needs formatting stubs
to keep CBMC tractable, and compressed-batch index handling.

### E. Go/Rust acceptance equivalence — Phase 2a (differential oracle)

The two implementations accept exactly the same tuples. Covered by differential
testing of the executable model against both, not by proof.

## Regression corpus (model must reject)

Concrete malicious proofs, each targeting one invariant. To be encoded as Lean
`example … = false` and as fixtures for the Phase 2a oracle.

- [ ] **A1-split:** NoPrefix length with variable-length prehash (e.g. NoHash on
      both fields) — re-split `key ++ value` to forge a different pair under one
      root. (A spec with this shape must be rejected by `WellFormed`.)
- [ ] **A2-depthconfusion:** an inner op whose prefix begins with the leaf
      prefix; must fail `ensure_inner`.
- [ ] **A3-childsize:** inner suffix length not a multiple of `child_size`; must
      fail `ensure_inner`.
- [ ] **A3-prefixwindow:** inner prefix length outside `[min, max + maxLeftChild]`.
- [ ] **C-negative:** spec with non-positive `child_size` or
      `max_prefix_length ≥ min_prefix_length + child_size`; must fail `WellFormed`.
- [ ] **depth-bounds:** `min_depth ≠ 0` with path length outside `[min, max]`.
- [ ] (from Zellic / Dragonberry — to be added once transcribed.)

## Proof status (Lean)

Model is complete (existence + non-existence). Proved with no `sorry`:
Theorem C (all three spec certificates); A1 leaf-encoding injectivity for both
`NoPrefix` (fixed-prehash) and `VarProto` (varint self-delimiting) shapes;
the path-fold backbone (`applyInner_inj`, `applyPath_sameops_inj`); and
**same-shape existence binding for all three shipped specs**
(`existence_binding_sameshape{,_noPrefix,_varProto}`). Non-existence padding /
empty-branch logic is exercised by the corpus.

### Remaining obligations

1. **General Theorem A — differing-path case (the one `sorry`).** Drop the
   `hpathEq`/`hleafEq` assumptions from `existence_binding_sameshape`. The crux:
   at a node where two proofs' inner ops differ but produce equal images
   (`op₁.prefix ++ c₁ ++ op₁.suffix = op₂.prefix ++ c₂ ++ op₂.suffix`),
   `WellFormed` + `ensureInner` (prefix window, `suffix % child_size = 0`,
   `max < min + child_size`) must force `op₁ = op₂` and `c₁ = c₂` (positional
   unambiguity, A3) — else a collision. This is the hardest piece; prove the
   positional lemma first in isolation, binary specs first.
2. **Theorem B (non-existence soundness).** Formalize the ordered-tree semantics
   an `InnerSpec` describes (left-most / right-most / adjacency under
   `child_order`, `empty_child` for sparse trees), then prove: an accepted
   non-existence proof for `k` plus an accepted existence proof for `k` ⇒
   collision. Respect `prehash_key_before_comparison` (guarantee is over hashed
   keys for SMT/JMT).
3. **Transcribe Zellic findings** into Properties / corpus.
4. **Batch/compressed** verification — model + decide whether in proof scope
   (RFC open question 3).

## Open items (cross-phase)

- Phase 2a differential oracle. The executable model now exists — a validated
  pure-Lean SHA-256 (`lean/Ics23/Sha256.lean`) and `concreteHash`, with
  end-to-end runs in `lean/Ics23/Executable.lean` (existence and non-existence,
  including forgery rejection). Remaining: feed it the `testdata/` vectors the
  Rust/Go suites use (needs a protobuf→simple-JSON bridge and a Lean reader) and
  compare accept/reject across all three implementations in CI.
- Phase 3 Kani harnesses for Rust panic/overflow safety.
