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
  - Byte-ordering facts behind the neighbor checks: `bytesLt_irrefl`,
    `bytesLt_ne` (`NonExistSound.lean`).
- **Stated, proof in progress (the two `sorry`s):**
  - the *general* Theorem A (`existence_binding`) — remaining gap is the
    differing-path-structure case (positional unambiguity, A3);
  - Theorem B, non-existence soundness (`nonexistence_sound`) — needs the
    ordered-tree semantics an `InnerSpec` describes.
- **CI:** `.github/workflows/lean.yml` builds all proofs and fails if any
  unexpected `sorry` appears (exactly two are whitelisted).
- **Next:** close Theorem A's differing-path case; prove Theorem B; build the
  differential oracle (Phase 2a).
