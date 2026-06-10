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

## Status

- **Proved:** spec well-formedness certificates for the three shipped specs
  (`iavl_wellFormed`, `tendermint_wellFormed`, `smt_wellFormed`); the inner
  preimage cancellation lemma (`innerImage_inj`).
- **Stated, proof in progress:** Theorem A, existence binding
  (`existence_binding`).
- **Next:** model the non-existence verifier and state Theorem B; complete
  Theorem A; build the differential oracle (Phase 2a).
