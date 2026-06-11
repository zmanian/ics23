# ICS23 formal model (Lean 4)

A mechanized model of the ICS23 verifier with machine-checked soundness proofs,
per [`docs/rfc/001-formal-verification.md`](../docs/rfc/001-formal-verification.md).
Property catalogue: [`docs/verification/properties.md`](../docs/verification/properties.md).

## Build

Requires [`elan`](https://github.com/leanprover/elan) (the toolchain is pinned in
`lean-toolchain`; `lake` fetches it automatically).

```sh
cd lean
lake build
```

A clean build prints one expected warning — `existence_binding` (Theorem A) still
uses `sorry` while its proof is being landed. Everything else is proof-complete.

## Layout

| File | Mirrors | Contents |
|------|---------|----------|
| `Ics23/Types.lean` | `proofs.proto`, `cosmos.ics23.v1.rs` | proto types |
| `Ics23/Ops.lean` | `rust/src/ops.rs` | `applyLeaf`, `applyInner`, `doHash` family, `doLength` |
| `Ics23/Verify.lean` | `rust/src/verify.rs` | existence verifier |
| `Ics23/Specs.lean` | `rust/src/api.rs` | IAVL / Tendermint / SMT specs |
| `Ics23/Soundness.lean` | — | `WellFormed`, collisions, Theorems A and C |

The model is parameterized over an abstract hash family and makes no
collision-resistance assumption: soundness theorems conclude by exhibiting a
`HashCollision`. See the modeling-assumptions section of the property catalogue
for where (and why) the model intentionally differs from the Rust.

| `Ics23/NonExist.lean` | `rust/src/verify.rs` | non-existence verifier |
| `Ics23/Corpus.lean` | — | regression corpus (proven accept/reject facts) |

## Status

- **Model complete:** existence and non-existence verifiers, both executable
  over an abstract hash family.
- **Proved:**
  - Spec well-formedness certificates for all three shipped specs (Theorem C:
    `iavl_wellFormed`, `tendermint_wellFormed`, `smt_wellFormed`).
  - Regression corpus: spec-level invariant violations (domain separation,
    child-size, prefix-window, malformed specs, depth bounds) as machine-checked
    facts (`Ics23/Corpus.lean`).
  - Building blocks of Theorem A: `innerImage_inj` (preimage cancellation),
    `applyInner_inj` (one step injective up to a collision), and
    `applyPath_sameops_inj` (folding a shared op-list is injective up to a
    collision) — the inductive backbone.
  - The varint length prefix is self-delimiting (`varintEncode_append_inj`,
    `Varint.lean`), giving leaf-encoding injectivity (A1) for length-prefixed
    specs; `doLength_varProto_inj` / `doLength_noPrefix_inj`.
  - **Same-shape existence binding (Theorem A) for all three shipped leaf
    shapes**: `existence_binding_sameshape` (general, parameterized by length
    injectivity) with corollaries `existence_binding_sameshape_noPrefix` (SMT/
    JMT) and `existence_binding_sameshape_varProto` (IAVL / Tendermint). Two
    proofs sharing tree shape that bind one key to two values force a hash
    collision — the value-swap forgery, end to end.
  - **Equal-length binding** `existence_binding_eqlen` — strengthens the above
    to proofs of equal *depth* with arbitrary (differing) inner ops, concluding
    the honest disjunction `HashCollision ∨ PositionalAmbiguity` (the F3
    obstacle). Built on `applyPath_eqlen_merge`.
  - **Same-leaf binding, any depth** `existence_binding_sameleaf` — the strongest
    result: same leaf op, *arbitrary differing-length* paths ⇒ `HashCollision ∨
    PositionalAmbiguity`. Built on the root-side structural core `applyPath_merge`
    (+ `applyPath_snoc`) and leaf/inner domain separation
    (`leafHash_innerImage_collision`). Instantiated for all three shipped specs:
    `existence_binding_{iavl,tendermint,smt}` (side conditions closed by `decide`).
  - **Finding F3 is formalized and machine-checked** (`PositionalAmbiguity`,
    witnesses in `Executable.lean`/`IavlPrefix.lean`): the general
    `existence_binding` is correctly stated as a disjunction, since a
    collision-only conclusion is provably too strong byte-level.
  - Byte-ordering facts behind the neighbor checks: `bytesLt_irrefl`,
    `bytesLt_ne` (`NonExistSound.lean`).
  - **General existence binding — fully proved** (`existence_binding_shaped`):
    for the production-spec shape, two proofs binding one key to two values under
    one root — with *no* assumption on their leaf ops or paths — yield the honest
    three-way disjunction `HashCollision ∨ PositionalAmbiguity ∨ LeafAmbiguity`.
    The ambiguity arms are real machine-checkable obstructions (F3 + leaf-level
    analogue); collapsing them needs the symbolic-Merkle model. Built on
    `applyPath_merge`, `ensureLeaf_eq`, `leafHash_innerImage_collision`.
- **Stated, proof in progress (the one remaining `sorry`):**
  - Theorem B, non-existence soundness (`nonexistence_sound`) — needs the
    ordered-tree semantics an `InnerSpec` describes / the symbolic-Merkle model.
- **Executable end to end:** a concrete SHA-256 (`Sha256.lean`, validated
  against the vectors in `rust/src/ops.rs`) and `concreteHash` make the verifier
  runnable; `Executable.lean` computes real roots and refutes value-swap /
  wrong-shape forgeries by `native_decide`. This is the seed of the Phase 2a
  differential oracle.
- **CI:** `.github/workflows/lean.yml` builds all proofs and fails if any
  unexpected `sorry` appears (exactly one is whitelisted).
- **Next:** prove Theorem B (`nonexistence_sound`); drive the executable model
  against the Rust/Go implementations (Phase 2a).
