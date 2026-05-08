package payaudit

import (
	"fmt"
	"math/big"
	"os"
	"testing"
	"time"

	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/logger"
)

var benchSetup *Setup

func TestMain(m *testing.M) {
	logger.Disable()
	var err error
	benchSetup, err = CompileCircuits()
	if err != nil {
		panic(err)
	}
	os.Exit(m.Run())
}

// ============================================================================
// TABLE II : per-circuit Generation / Verification / Constraints
// ============================================================================

type circuitRow struct {
	name   string
	nbCons int
	gen    time.Duration
	ver    time.Duration
}

func TestPrintCircuitTable(t *testing.T) {
	if testing.Short() {
		t.Skip()
	}
	const runs = 5

	sender, err := NewState(benchSetup, 1_000_000)
	if err != nil {
		t.Fatal(err)
	}
	receiver, err := NewState(benchSetup, 0)
	if err != nil {
		t.Fatal(err)
	}
	amount := big.NewInt(100)
	rcm := big.NewInt(123456)
	pkR := big.NewInt(789012)

	rNew, _ := randField()
	rDep, _ := randField()
	blind, _ := randField()
	balS := new(big.Int).Sub(sender.Bal, amount)
	ctrS := new(big.Int).Add(sender.Ctr, big.NewInt(1))
	scmSNew := nativeCommit(rNew, balS, ctrS, sender.A, sender.Pk, sender.H, sender.E, sender.Scm, rcm)
	dcmSNew := nativeCommit(rDep, sender.Scm, rcm)
	pcm := nativeCommit(blind, amount, rcm, scmSNew, sender.E)

	scmSNewSig, err := bankSign(benchSetup.BankSk, scmSNew)
	if err != nil {
		t.Fatal(err)
	}
	kInline, _ := newJubScalar()
	tsInline := TracingTag(sender.A, ctrS)
	psiInline := ElGamalEncrypt(benchSetup.PkTh, amount, sender.Pk, pkR, kInline)

	rNew2, _ := randField()
	rDep2, _ := randField()
	balR := new(big.Int).Add(receiver.Bal, amount)
	scmRNew := nativeCommit(rNew2, balR, receiver.Ctr, receiver.A, receiver.Pk, receiver.H, receiver.E, receiver.Scm, scmSNew)
	dcmRNew := nativeCommit(rDep2, receiver.Scm, scmSNew)

	dummyPayment := &PaymentData{
		Rcm: rcm, BlindPm: blind, ScmSOld: sender.Scm, ScmSNew: scmSNew,
		DcmSNew: dcmSNew, ES: sender.E,
	}

	r0, _ := randField()
	a0, _ := randField()
	pkU0, _ := randField()
	H0 := big.NewInt(1_000_000_000)
	e0 := big.NewInt(1)
	c0 := big.NewInt(1234)
	scm0 := nativeCommit(r0, big.NewInt(0), big.NewInt(0), a0, pkU0, H0, e0, big.NewInt(0), c0)

	bench := func(name string, cs interface{ GetNbConstraints() int }, prove func() (groth16.Proof, error), verify func(groth16.Proof) error) circuitRow {
		var p groth16.Proof
		var gen, ver time.Duration
		for i := 0; i < runs; i++ {
			t0 := time.Now()
			pp, err := prove()
			if err != nil {
				t.Fatal(err)
			}
			gen += time.Since(t0)
			p = pp
		}
		for i := 0; i < runs; i++ {
			t0 := time.Now()
			if err := verify(p); err != nil {
				t.Fatal(err)
			}
			ver += time.Since(t0)
		}
		return circuitRow{name: name, nbCons: cs.GetNbConstraints(), gen: gen / runs, ver: ver / runs}
	}

	rows := []circuitRow{
		bench("Enroll", benchSetup.EnrollCS,
			func() (groth16.Proof, error) { return proveEnroll(benchSetup, scm0, pkU0, H0, e0, c0, a0, r0) },
			func(p groth16.Proof) error { return verifyEnroll(benchSetup, scm0, pkU0, H0, e0, c0, p) },
		),
		bench("Payment", benchSetup.PmCS,
			func() (groth16.Proof, error) { return provePm(benchSetup, amount, rcm, scmSNew, sender.E, blind, pcm) },
			func(p groth16.Proof) error { return verifyPm(benchSetup, pcm, p) },
		),
		bench("Payment creation state transition", benchSetup.CreateCS,
			func() (groth16.Proof, error) {
				return proveCreate(benchSetup, sender, rcm, amount, rNew, rDep, blind, scmSNew, dcmSNew, pcm)
			},
			func(p groth16.Proof) error { return verifyCreate(benchSetup, scmSNew, dcmSNew, pcm, p) },
		),
		bench("Payment creation state transition (inline ElGamal/tag)", benchSetup.CreateInCS,
			func() (groth16.Proof, error) {
				return proveCreateInline(benchSetup, sender, rcm, amount, pkR, kInline, rNew, rDep, blind, scmSNew, dcmSNew, pcm, tsInline, psiInline)
			},
			func(p groth16.Proof) error {
				return verifyCreateInline(benchSetup, scmSNew, dcmSNew, pcm, tsInline, psiInline, p)
			},
		),
		bench("Payment creation dependency", benchSetup.DepCrCS,
			func() (groth16.Proof, error) { return proveDepCreate(benchSetup, sender, rcm, rDep, dcmSNew) },
			func(p groth16.Proof) error { return verifyDepCreate(benchSetup, dcmSNew, p) },
		),
		bench("Payment completion state transition", benchSetup.DoneCS,
			func() (groth16.Proof, error) {
				return proveComplete(benchSetup, receiver, dummyPayment, amount, rNew2, rDep2, scmRNew, dcmRNew, pcm)
			},
			func(p groth16.Proof) error { return verifyComplete(benchSetup, scmRNew, dcmRNew, pcm, p) },
		),
		bench("Payment completion dependency", benchSetup.DepDoneCS,
			func() (groth16.Proof, error) {
				return proveDepComplete(benchSetup, receiver.Sig, scmSNewSig, receiver.Scm, scmSNew, rDep2, dcmRNew)
			},
			func(p groth16.Proof) error { return verifyDepComplete(benchSetup, dcmRNew, p) },
		),
	}

	// Schnorr link proof (out-of-circuit)
	{
		k, _ := newJubScalar()
		ts := TracingTag(sender.A, ctrS)
		psi := ElGamalEncrypt(benchSetup.PkTh, amount, sender.Pk, pkR, k)
		aCtr := new(big.Int).Mul(sender.A, ctrS)
		transcript := linkTranscript(scmSNew, pcm)
		var bundle *SchnorrBundle
		var gen, ver time.Duration
		for i := 0; i < runs; i++ {
			t0 := time.Now()
			b, err := ProvePaymentLink(benchSetup.PkTh, ts, psi, amount, sender.Pk, pkR, aCtr, k, transcript)
			if err != nil {
				t.Fatal(err)
			}
			gen += time.Since(t0)
			bundle = b
		}
		for i := 0; i < runs; i++ {
			t0 := time.Now()
			if !VerifyPaymentLink(benchSetup.PkTh, ts, psi, amount, pkR, bundle, transcript) {
				t.Fatal("link verify failed")
			}
			ver += time.Since(t0)
		}
		rows = append(rows, circuitRow{name: "Link (Schnorr, out-of-circuit)", nbCons: 0, gen: gen / runs, ver: ver / runs})
	}

	fmt.Println()
	fmt.Println("===== TABLE II : per-proof generation / verification / constraints =====")
	fmt.Printf("%-42s | %-14s | %-16s | %-12s\n", "Proof Circuit", "Generation (s)", "Verification (s)", "Constraints")
	fmt.Println("-------------------------------------------+----------------+------------------+--------------")
	for _, r := range rows {
		cons := "-"
		if r.nbCons > 0 {
			cons = fmt.Sprintf("%d", r.nbCons)
		}
		fmt.Printf("%-42s | %-14.4f | %-16.4f | %-12s\n", r.name, r.gen.Seconds(), r.ver.Seconds(), cons)
	}
	fmt.Println()
}

// ============================================================================
// TABLE III : end-to-end CreatePayment / AcceptPayment / CompletePayment
// ============================================================================

type endRow struct {
	createS       float64
	acceptS       float64
	completeS     float64
	endAcceptedS  float64
	endCompletedS float64
	requestKB     float64
	createKB      float64
}

func TestPrintEndToEndTable(t *testing.T) {
	if testing.Short() {
		t.Skip()
	}
	sizes := []int{1, 51, 101}
	const runs = 3

	fmt.Println()
	fmt.Println("===== TABLE III : end-to-end offline payment latency =====")
	fmt.Printf("%-8s | %-12s | %-12s | %-12s | %-15s | %-15s | %-12s | %-12s\n",
		"history", "Create (s)", "Accept (s)", "Complete (s)", "E2E accept (s)", "E2E complete (s)", "Req (kB)", "Pay (kB)")
	fmt.Println("---------+--------------+--------------+--------------+-----------------+-----------------+--------------+--------------")
	for _, n := range sizes {
		r := measureEnd(t, n, runs)
		fmt.Printf("%-8d | %-12.4f | %-12.4f | %-12.4f | %-15.4f | %-15.4f | %-12.4f | %-12.4f\n",
			n, r.createS, r.acceptS, r.completeS, r.endAcceptedS, r.endCompletedS, r.requestKB, r.createKB)
	}
	fmt.Println()
}

func TestInlinePaymentFlow(t *testing.T) {
	sender, err := NewState(benchSetup, 1_000_000)
	if err != nil {
		t.Fatal(err)
	}
	amount := big.NewInt(100)
	rcm := big.NewInt(123456)
	pkR := big.NewInt(789012)
	payment, _, err := CreatePaymentInline(benchSetup, sender, rcm, amount, pkR, nil)
	if err != nil {
		t.Fatal(err)
	}
	if payment.LinkProof != nil {
		t.Fatal("inline payment must not include Schnorr proof")
	}
	if err := AcceptPaymentInline(benchSetup, payment, amount, pkR); err != nil {
		t.Fatal(err)
	}
}

func measureEnd(t *testing.T, historyLen, runs int) endRow {
	t.Helper()
	sender, err := NewState(benchSetup, 1_000_000)
	if err != nil {
		t.Fatal(err)
	}
	receiver, err := NewState(benchSetup, 0)
	if err != nil {
		t.Fatal(err)
	}
	history, err := MakeHistory(benchSetup, historyLen)
	if err != nil {
		t.Fatal(err)
	}
	amount := big.NewInt(100)
	rcm := big.NewInt(123456)
	pkR := big.NewInt(789012)

	var createT, acceptT, completeT time.Duration
	var msgKB float64
	for i := 0; i < runs; i++ {
		t0 := time.Now()
		payment, _, err := CreatePayment(benchSetup, sender, rcm, amount, pkR, history)
		if err != nil {
			t.Fatal(err)
		}
		createT += time.Since(t0)

		t0 = time.Now()
		if err := AcceptPayment(benchSetup, payment, amount, pkR); err != nil {
			t.Fatal(err)
		}
		acceptT += time.Since(t0)

		t0 = time.Now()
		rNew, _ := randField()
		rDep, _ := randField()
		balNew := new(big.Int).Add(receiver.Bal, amount)
		scmNew := nativeCommit(rNew, balNew, receiver.Ctr, receiver.A, receiver.Pk, receiver.H, receiver.E, receiver.Scm, payment.ScmSNew)
		dcmNew := nativeCommit(rDep, receiver.Scm, payment.ScmSNew)
		pcm := nativeCommit(payment.BlindPm, amount, payment.Rcm, payment.ScmSNew, payment.ES)
		if _, err := proveComplete(benchSetup, receiver, payment, amount, rNew, rDep, scmNew, dcmNew, pcm); err != nil {
			t.Fatal(err)
		}
		completeT += time.Since(t0)

		msgKB = float64(PaymentMessageSize(payment)) / 1024
	}
	d := time.Duration(runs)
	c := createT / d
	a := acceptT / d
	co := completeT / d
	return endRow{
		createS:       c.Seconds(),
		acceptS:       a.Seconds(),
		completeS:     co.Seconds(),
		endAcceptedS:  (c + a).Seconds(),
		endCompletedS: (c + a + co).Seconds(),
		requestKB:     float64(RequestSize(&PaymentRequest{Rcm: rcm, PkR: pkR})) / 1024,
		createKB:      msgKB,
	}
}
