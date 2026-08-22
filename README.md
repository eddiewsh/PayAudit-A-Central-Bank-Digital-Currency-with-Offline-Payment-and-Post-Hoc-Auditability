# PayAudit: A Central Bank Digital Currency with Offline Payment and Post-Hoc Auditability

Wong Sze Ho · Supervisor: Prof. Sherman Chow  
Department of Information Engineering, The Chinese University of Hong Kong

Go prototype (`gnark` / Groth16 / BN254) of an **account-based** CBDC that supports cash-like offline payments and lawful post-hoc audit — without trusted hardware.

[Poster (PDF)](docs/IERG4999_poster7.pdf)

<p align="center">
  <img src="docs/figures/poster-preview.jpg" alt="IERG4999 PayAudit poster" width="720">
</p>

## Summary

PayAudit separates ordinary payment verification from exceptional audit. The Central Bank sees no private data; authorised maintainers can decrypt a transaction only under a lawful order (any 3 of 5). Everyday payments are cash-like anonymous; audit happens only after settlement.

## Goal

Offline private CBDC with three properties at once, in **pure cryptography** (no TEE / secure-element manufacturer):

- **Offline payments** — users transact without network access.
- **Cash-like privacy** — no one automatically sees balances or what was bought.
- **Accountability when needed** — authorities can investigate under strict distributed authorisation.

PayOff achieves offline privacy but has no post-hoc audit. TEE-backed designs provide accountability but rest on a trusted hardware manufacturer — a supply-chain assumption that is unacceptable for a sovereign CBDC.

## Comparison

<p align="center">
  <img src="docs/figures/figure1-comparison.png" alt="Figure 1: Scheme comparison" width="820">
</p>

<p align="center"><em>Figure 1. Comparison with PEReDi / Platypus and PayOff.</em></p>

| Scheme | Offline | Audit &amp; Trace | Mechanism / limitation |
| --- | --- | --- | --- |
| PEReDi / Platypus | ✗ | ✓ | Post-hoc audit via threshold ElGamal; **must be online** during payment |
| PayOff | ✓ | ✗ | Offline chained settlement; resists TEE compromise but **no audit** |
| **PayAudit (ours)** | ✓ | ✓ | First to combine both: audit ciphertext \(\psi\) and traceable double-spend tag \(T\) on top of PayOff |

## System overview

**Actors**

- **Users** (payer / payee)
- **Central Bank (CB)** — verifies proofs and checks double-spending; trusted to verify correctly, **not** trusted to protect privacy
- **Maintainers / authorities** — any 3 of 5 must cooperate to audit or trace

**Offline payment steps**

1. **Committed wallet state** — balance is hidden inside a cryptographic commitment.
2. **Zero-knowledge update** — prove correct deduction and no overspend without revealing the balance.
3. **Embedded tag \(T\) and audit ciphertext \(\psi\)** — \(\psi\) threshold-locks amount and identities; \(T\) detects double-spend and anchors user tracing.
4. **Delayed settlement** — CB verifies proofs and checks \(T\) for double-spend.

## Offline payment protocol

<p align="center">
  <img src="docs/figures/figure2-protocol.png" alt="Figure 2: PayAudit protocol flow" width="820">
</p>

<p align="center"><em>Figure 2. PayAudit protocol flow.</em></p>

1. Receiver requests a payment (commitment + value).
2. Sender creates the payment: commitments, ZKPs, double-spend tag \(T\), audit ciphertext \(\psi\), and dependency history.
3. Receiver verifies proofs and the dependency chain, updates local state, and stores \(T\) and \(\psi\).
4. On reconnection, the receiver queries the ledger and requests a CB signature.
5. CB verifies proofs, checks \(T\) for double-spend, signs accepted states, and writes to the ledger. \(T\) is embedded at spend time and detected only at reconnection — double-spending is punished post-hoc, not prevented online.
6. On a lawful audit request or detected double-spend, maintainers cooperate to decrypt \(\psi\) and trace user history.

This repository implements the offline pipeline:

- `CreatePayment` / `CreatePaymentInline`
- `AcceptPayment` / `AcceptPaymentInline`
- `CompletePayment`

State commitments form a verifiable chain (PayOff-style). The sender alone produces \(\psi\) (threshold ElGamal of \(v, pk_S, pk_R\)); the receiver stores it and carries it in the dependency history.

## Security and privacy

<p align="center">
  <img src="docs/figures/figure3-security.png" alt="Figure 3: PayAudit security overview" width="820">
</p>

<p align="center"><em>Figure 3. Security overview.</em></p>

| Requirement | Mechanism | Meaning |
| --- | --- | --- |
| Hide balance | Committed wallet state | Balance sits in a commitment on the ledger |
| Prevent overspending | Zero-knowledge proof | Prove a valid resulting balance without revealing values |
| Detect double-spending | Deterministic tag \(T = g^{a \cdot ctr}\) | Reusing an old state yields the same \(T\) |
| Hide identities | Threshold ElGamal \(\psi\) | Amount and identities are locked; no single party can open them |
| Enable lawful audit | \((t+1)\)-threshold decryption | Only a quorum of maintainers unlocks \(\psi\) |
| Trace user history | Secret \(a\) reconstruction | Regulator computes candidate \(T\) values and scans the ledger |
| Prevent tampering | Dependency chain | Each state links to the previous; a break is detectable |

**Threat model.** 5 maintainers; any 3 must cooperate to audit or trace. At most 2 may be malicious or unavailable (\(t = 2\), \(D = 5t+1 = 5\)). Even if CB colludes with all malicious maintainers (up to 2), privacy remains intact.

**Efficient cryptography.** Groth16 circuits use native-field arithmetic only. Group operations for \(T\) and \(\psi\) are moved out-of-circuit and linked by a compact Schnorr proof (\(\approx 64\) bytes), so proofs stay mobile-speed without sacrificing security.

## Performance

Tested on a laptop with AMD Ryzen 7 4800H @ 2.90 GHz (Zen 2, 16 GB). Go prototype: `gnark` / Groth16 / BN254.

<p align="center">
  <img src="docs/figures/figure4-performance.png" alt="Figure 4: PayAudit performance results" width="820">
</p>

<p align="center"><em>Figure 4. Performance results.</em></p>

| Metric | Result |
| --- | --- |
| Single offline payment (create + accept + complete) | \(< 0.3\) s |
| Settlement of a 100-payment chain | \(< 0.6\) s |
| Message size for 100-payment history | \(\sim 105\) KB (\(\sim 1\) KB per payment) |

| Circuit-size comparison (creation proof) | Constraints / cost |
| --- | --- |
| ElGamal &amp; tag **inside** the ZK circuit | 33,714 |
| ElGamal &amp; tag **outside** + Schnorr proof | 19,306 |
| Constraint reduction | \(\sim 43\%\) |
| Schnorr generation / verification | 0.0006 s / 0.0012 s (negligible) |

PayOff similar creation \(\approx 0.21\) s on a Ryzen 7 PRO 7730U (Zen 3, 32 GB) ([arXiv:2408.06956](https://arxiv.org/abs/2408.06956), Table III); ours \(\approx 0.12\) s with added audit/trace. Direct comparison is approximate; the older CPU makes the speedup conservative. Performance matches a scheme without audit (Schnorr cost is negligible). 100 offline payments produce \(\sim 105\) KB of proof data — comparable to a compressed image, well within mobile storage.

## Contributions

1. **First unified account-based design** (balance per user, not per coin) — offline chained settlement plus threshold post-hoc audit in one scheme.
2. **Efficient cryptography** — expensive wallet-linking is separated from proof generation; a compact Schnorr proof bridges them.
3. **Balanced privacy vs. regulation** — everyday payments are cash-like anonymous; lawful access requires distributed authorisation, preventing unilateral surveillance.

## Reproduce tables

Requires Go 1.24+ (`go.mod`).

```bash
go test ./...
```

```bash
go test ./... -run TestPrintCircuitTable -count=1
go test ./... -run TestPrintEndToEndTable -count=1
```

Both table tests are skipped under `-short`.

## References

1. C. Beer et al., *PayOff: A Regulated Central Bank Digital Currency with Private Offline Payments*, AsiaCCS, 2026. [arXiv:2408.06956](https://arxiv.org/abs/2408.06956)
2. A. Sarencheh et al., *PEReDi: Privacy-Enhanced, Regulated and Distributed Central Bank Digital Currencies*, ACM CCS, 2022.
3. K. Wüst et al., *Platypus: A Central Bank Digital Currency with Unlinkable Transactions and Privacy-Preserving Regulation*, ACM CCS, 2022.
