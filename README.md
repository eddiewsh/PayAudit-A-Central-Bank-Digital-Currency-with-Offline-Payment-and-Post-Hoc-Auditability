## PayAudit: Offline CBDC with Post-Hoc Auditability (Prototype/Benchmark)

This repository contains a Go prototype of PayAudit (built with `gnark` / Groth16 / BN254). The goal is to benchmark the offline payment pipeline (CreatePayment / AcceptPayment / CompletePayment) and the cost of the underlying zero-knowledge proofs (generation/verification).

## Paper / Design Summary

- State commitments form a verifiable chain (inspired by PayOff).
- A single tracing tag \(T = g^{a_U \cdot ctr}\) supports both double-spend detection and user tracing.
- The audit ciphertext \(\psi\) is produced by the sender only (encrypting \(v, pk_S, pk_R\) under threshold ElGamal); the receiver stores it and carries it in the dependency history.
- Distributed maintainers: threshold \(t+1\) out of \(D=5t+1\).
- Groth16 circuits use native-field arithmetic only; group operations (\(T,\psi\)) are moved out-of-circuit and linked via a Schnorr proof to keep circuits small.

Related work:
- PayOff (2024), PEReDi (2022), Platypus (2022)

## Testing / Reproducing Tables (Go)

Requirement: Go 1.24+ (see `go.mod`).

### Quick tests (no tables)

```bash
go test ./...
```

### Print benchmark tables (slower)

```bash
go test ./... -run TestPrintCircuitTable -count=1
go test ./... -run TestPrintEndToEndTable -count=1
```

Note: both tests are skipped when running in `-short` mode.

