package payaudit

import (
	"bytes"
	"crypto/rand"
	"errors"
	"math/big"

	cryptotw "github.com/consensys/gnark-crypto/ecc/twistededwards"
	"github.com/consensys/gnark-crypto/signature"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/algebra/native/twistededwards"
	"github.com/consensys/gnark/std/hash/mimc"
	eddsaStd "github.com/consensys/gnark/std/signature/eddsa"
)

const SyncTol int64 = 5

type Setup struct {
	EnrollCS   constraint.ConstraintSystem
	EnrollPK   groth16.ProvingKey
	EnrollVK   groth16.VerifyingKey
	CreateCS   constraint.ConstraintSystem
	CreatePK   groth16.ProvingKey
	CreateVK   groth16.VerifyingKey
	CreateInCS constraint.ConstraintSystem
	CreateInPK groth16.ProvingKey
	CreateInVK groth16.VerifyingKey
	DepCrCS    constraint.ConstraintSystem
	DepCrPK    groth16.ProvingKey
	DepCrVK    groth16.VerifyingKey
	PmCS       constraint.ConstraintSystem
	PmPK       groth16.ProvingKey
	PmVK       groth16.VerifyingKey
	DoneCS     constraint.ConstraintSystem
	DonePK     groth16.ProvingKey
	DoneVK     groth16.VerifyingKey
	DepDoneCS  constraint.ConstraintSystem
	DepDonePK  groth16.ProvingKey
	DepDoneVK  groth16.VerifyingKey
	BankSk     signature.Signer
	BankPk     signature.PublicKey
	BankPkBin  []byte
	PkTh       *Point
}

type State struct {
	Scm      *big.Int
	Sig      []byte
	Bal      *big.Int
	Ctr      *big.Int
	A        *big.Int
	Pk       *big.Int
	H        *big.Int
	E        *big.Int
	ScmPrev  *big.Int
	Ccm      *big.Int
	Blinding *big.Int
}

type PaymentRequest struct {
	Rcm *big.Int
	PkR *big.Int
}

type HistoryProof struct {
	Rcm        *big.Int
	BlindPm    *big.Int
	ScmSOld    *big.Int
	ScmSNew    *big.Int
	DcmSNew    *big.Int
	TS         *Point
	Psi        *ElGamalCipher
	ES         *big.Int
	Amount     *big.Int
	PkR        *big.Int
	StateProof groth16.Proof
	DepProof   groth16.Proof
	PmProof    groth16.Proof
	LinkProof  *SchnorrBundle
}

type PaymentData struct {
	Rcm        *big.Int
	BlindPm    *big.Int
	ScmSOld    *big.Int
	ScmSNew    *big.Int
	DcmSNew    *big.Int
	TS         *Point
	Psi        *ElGamalCipher
	ES         *big.Int
	StateProof groth16.Proof
	DepProof   groth16.Proof
	PmProof    groth16.Proof
	LinkProof  *SchnorrBundle
	History    []HistoryProof
}

// ============================================================================
// Circuits
// ============================================================================

type CircuitEnroll struct {
	Scm0 frontend.Variable `gnark:",public"`
	PkU  frontend.Variable `gnark:",public"`
	H    frontend.Variable `gnark:",public"`
	E    frontend.Variable `gnark:",public"`
	C    frontend.Variable `gnark:",public"`
	A    frontend.Variable
	R0   frontend.Variable
}

func (c *CircuitEnroll) Define(api frontend.API) error {
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	zero := frontend.Variable(0)
	h.Reset()
	h.Write(c.R0, zero, zero, c.A, c.PkU, c.H, c.E, zero, c.C)
	api.AssertIsEqual(h.Sum(), c.Scm0)
	return nil
}

type CircuitStateCreate struct {
	ScmNew  frontend.Variable  `gnark:",public"`
	DcmNew  frontend.Variable  `gnark:",public"`
	Pcm     frontend.Variable  `gnark:",public"`
	PkCB    eddsaStd.PublicKey `gnark:",public"`
	Sig     eddsaStd.Signature
	ScmOld  frontend.Variable
	Bal     frontend.Variable
	Ctr     frontend.Variable
	A       frontend.Variable
	PkS     frontend.Variable
	H       frontend.Variable
	ES      frontend.Variable
	ScmPre  frontend.Variable
	CcmOld  frontend.Variable
	ROld    frontend.Variable
	RNew    frontend.Variable
	RDep    frontend.Variable
	Rcm     frontend.Variable
	V       frontend.Variable
	BlindPm frontend.Variable
}

func (c *CircuitStateCreate) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, cryptotw.BN254)
	if err != nil {
		return err
	}
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}

	h.Reset()
	h.Write(c.ROld, c.Bal, c.Ctr, c.A, c.PkS, c.H, c.ES, c.ScmPre, c.CcmOld)
	api.AssertIsEqual(h.Sum(), c.ScmOld)

	h.Reset()
	if err := eddsaStd.Verify(curve, c.Sig, c.ScmOld, c.PkCB, &h); err != nil {
		return err
	}

	h.Reset()
	h.Write(c.RNew, api.Sub(c.Bal, c.V), api.Add(c.Ctr, 1), c.A, c.PkS, c.H, c.ES, c.ScmOld, c.Rcm)
	api.AssertIsEqual(h.Sum(), c.ScmNew)

	h.Reset()
	h.Write(c.RDep, c.ScmOld, c.Rcm)
	api.AssertIsEqual(h.Sum(), c.DcmNew)

	h.Reset()
	h.Write(c.BlindPm, c.V, c.Rcm, c.ScmNew, c.ES)
	api.AssertIsEqual(h.Sum(), c.Pcm)

	api.AssertIsLessOrEqual(c.V, c.Bal)
	api.AssertIsDifferent(c.V, 0)
	api.AssertIsLessOrEqual(api.Sub(c.Bal, c.V), c.H)
	return nil
}

type CircuitStateCreateInline struct {
	ScmNew  frontend.Variable    `gnark:",public"`
	DcmNew  frontend.Variable    `gnark:",public"`
	Pcm     frontend.Variable    `gnark:",public"`
	PkCB    eddsaStd.PublicKey   `gnark:",public"`
	PkTh    twistededwards.Point `gnark:",public"`
	TS      twistededwards.Point `gnark:",public"`
	C1      twistededwards.Point `gnark:",public"`
	C2      twistededwards.Point `gnark:",public"`
	C3      twistededwards.Point `gnark:",public"`
	C4      twistededwards.Point `gnark:",public"`
	Sig     eddsaStd.Signature
	ScmOld  frontend.Variable
	Bal     frontend.Variable
	Ctr     frontend.Variable
	A       frontend.Variable
	PkS     frontend.Variable
	H       frontend.Variable
	ES      frontend.Variable
	ScmPre  frontend.Variable
	CcmOld  frontend.Variable
	ROld    frontend.Variable
	RNew    frontend.Variable
	RDep    frontend.Variable
	Rcm     frontend.Variable
	V       frontend.Variable
	PkR     frontend.Variable
	K       frontend.Variable
	BlindPm frontend.Variable
}

func (c *CircuitStateCreateInline) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, cryptotw.BN254)
	if err != nil {
		return err
	}
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}

	h.Reset()
	h.Write(c.ROld, c.Bal, c.Ctr, c.A, c.PkS, c.H, c.ES, c.ScmPre, c.CcmOld)
	api.AssertIsEqual(h.Sum(), c.ScmOld)

	h.Reset()
	if err := eddsaStd.Verify(curve, c.Sig, c.ScmOld, c.PkCB, &h); err != nil {
		return err
	}

	h.Reset()
	h.Write(c.RNew, api.Sub(c.Bal, c.V), api.Add(c.Ctr, 1), c.A, c.PkS, c.H, c.ES, c.ScmOld, c.Rcm)
	api.AssertIsEqual(h.Sum(), c.ScmNew)

	h.Reset()
	h.Write(c.RDep, c.ScmOld, c.Rcm)
	api.AssertIsEqual(h.Sum(), c.DcmNew)

	h.Reset()
	h.Write(c.BlindPm, c.V, c.Rcm, c.ScmNew, c.ES)
	api.AssertIsEqual(h.Sum(), c.Pcm)

	api.AssertIsLessOrEqual(c.V, c.Bal)
	api.AssertIsDifferent(c.V, 0)
	api.AssertIsLessOrEqual(api.Sub(c.Bal, c.V), c.H)

	base := twistededwards.Point{X: curve.Params().Base[0], Y: curve.Params().Base[1]}
	pkThK := curve.ScalarMul(c.PkTh, c.K)
	ts := curve.ScalarMul(base, api.Mul(c.A, api.Add(c.Ctr, 1)))
	c1 := curve.ScalarMul(base, c.K)
	c2 := curve.Add(curve.ScalarMul(base, c.V), pkThK)
	c3 := curve.Add(curve.ScalarMul(base, c.PkS), pkThK)
	c4 := curve.Add(curve.ScalarMul(base, c.PkR), pkThK)

	api.AssertIsEqual(ts.X, c.TS.X)
	api.AssertIsEqual(ts.Y, c.TS.Y)
	api.AssertIsEqual(c1.X, c.C1.X)
	api.AssertIsEqual(c1.Y, c.C1.Y)
	api.AssertIsEqual(c2.X, c.C2.X)
	api.AssertIsEqual(c2.Y, c.C2.Y)
	api.AssertIsEqual(c3.X, c.C3.X)
	api.AssertIsEqual(c3.Y, c.C3.Y)
	api.AssertIsEqual(c4.X, c.C4.X)
	api.AssertIsEqual(c4.Y, c.C4.Y)
	return nil
}

type CircuitDepCreate struct {
	DcmNew frontend.Variable  `gnark:",public"`
	PkCB   eddsaStd.PublicKey `gnark:",public"`
	Sig    eddsaStd.Signature
	ScmOld frontend.Variable
	Rcm    frontend.Variable
	RDep   frontend.Variable
}

func (c *CircuitDepCreate) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, cryptotw.BN254)
	if err != nil {
		return err
	}
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	if err := eddsaStd.Verify(curve, c.Sig, c.ScmOld, c.PkCB, &h); err != nil {
		return err
	}
	h.Reset()
	h.Write(c.RDep, c.ScmOld, c.Rcm)
	api.AssertIsEqual(h.Sum(), c.DcmNew)
	return nil
}

type CircuitPm struct {
	Pcm     frontend.Variable `gnark:",public"`
	V       frontend.Variable
	Rcm     frontend.Variable
	ScmSNew frontend.Variable
	ES      frontend.Variable
	BlindPm frontend.Variable
}

func (c *CircuitPm) Define(api frontend.API) error {
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	h.Reset()
	h.Write(c.BlindPm, c.V, c.Rcm, c.ScmSNew, c.ES)
	api.AssertIsEqual(h.Sum(), c.Pcm)
	return nil
}

type CircuitStateComplete struct {
	ScmNew  frontend.Variable  `gnark:",public"`
	DcmNew  frontend.Variable  `gnark:",public"`
	Pcm     frontend.Variable  `gnark:",public"`
	PkCB    eddsaStd.PublicKey `gnark:",public"`
	Sig     eddsaStd.Signature
	ScmOld  frontend.Variable
	Bal     frontend.Variable
	Ctr     frontend.Variable
	A       frontend.Variable
	PkR     frontend.Variable
	H       frontend.Variable
	ER      frontend.Variable
	ScmPre  frontend.Variable
	CcmOld  frontend.Variable
	ROld    frontend.Variable
	RNew    frontend.Variable
	RDep    frontend.Variable
	Rcm     frontend.Variable
	ScmSNew frontend.Variable
	V       frontend.Variable
	BlindPm frontend.Variable
	ES      frontend.Variable
}

func (c *CircuitStateComplete) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, cryptotw.BN254)
	if err != nil {
		return err
	}
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}

	h.Reset()
	h.Write(c.ROld, c.Bal, c.Ctr, c.A, c.PkR, c.H, c.ER, c.ScmPre, c.CcmOld)
	api.AssertIsEqual(h.Sum(), c.ScmOld)

	h.Reset()
	if err := eddsaStd.Verify(curve, c.Sig, c.ScmOld, c.PkCB, &h); err != nil {
		return err
	}

	h.Reset()
	h.Write(c.RNew, api.Add(c.Bal, c.V), c.Ctr, c.A, c.PkR, c.H, c.ER, c.ScmOld, c.ScmSNew)
	api.AssertIsEqual(h.Sum(), c.ScmNew)

	h.Reset()
	h.Write(c.RDep, c.ScmOld, c.ScmSNew)
	api.AssertIsEqual(h.Sum(), c.DcmNew)

	h.Reset()
	h.Write(c.BlindPm, c.V, c.Rcm, c.ScmSNew, c.ES)
	api.AssertIsEqual(h.Sum(), c.Pcm)

	api.AssertIsLessOrEqual(api.Add(c.Bal, c.V), c.H)

	shifted := api.Add(api.Sub(c.ES, c.ER), SyncTol)
	api.AssertIsLessOrEqual(shifted, 2*SyncTol)
	return nil
}

type CircuitDepComplete struct {
	DcmNew  frontend.Variable  `gnark:",public"`
	PkCB    eddsaStd.PublicKey `gnark:",public"`
	SigR    eddsaStd.Signature
	SigS    eddsaStd.Signature
	ScmROld frontend.Variable
	ScmSNew frontend.Variable
	RDep    frontend.Variable
}

func (c *CircuitDepComplete) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, cryptotw.BN254)
	if err != nil {
		return err
	}
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	h.Reset()
	if err := eddsaStd.Verify(curve, c.SigR, c.ScmROld, c.PkCB, &h); err != nil {
		return err
	}
	h.Reset()
	if err := eddsaStd.Verify(curve, c.SigS, c.ScmSNew, c.PkCB, &h); err != nil {
		return err
	}
	h.Reset()
	h.Write(c.RDep, c.ScmROld, c.ScmSNew)
	api.AssertIsEqual(h.Sum(), c.DcmNew)
	return nil
}

// ============================================================================
	// Setup / state initialisation
// ============================================================================

func CompileCircuits() (*Setup, error) {
	enrollCS, err := frontend.Compile(fieldMod, r1cs.NewBuilder, &CircuitEnroll{})
	if err != nil {
		return nil, err
	}
	enrollPK, enrollVK, err := groth16.Setup(enrollCS)
	if err != nil {
		return nil, err
	}
	createCS, err := frontend.Compile(fieldMod, r1cs.NewBuilder, &CircuitStateCreate{})
	if err != nil {
		return nil, err
	}
	createPK, createVK, err := groth16.Setup(createCS)
	if err != nil {
		return nil, err
	}
	createInCS, err := frontend.Compile(fieldMod, r1cs.NewBuilder, &CircuitStateCreateInline{})
	if err != nil {
		return nil, err
	}
	createInPK, createInVK, err := groth16.Setup(createInCS)
	if err != nil {
		return nil, err
	}
	depCrCS, err := frontend.Compile(fieldMod, r1cs.NewBuilder, &CircuitDepCreate{})
	if err != nil {
		return nil, err
	}
	depCrPK, depCrVK, err := groth16.Setup(depCrCS)
	if err != nil {
		return nil, err
	}
	pmCS, err := frontend.Compile(fieldMod, r1cs.NewBuilder, &CircuitPm{})
	if err != nil {
		return nil, err
	}
	pmPK, pmVK, err := groth16.Setup(pmCS)
	if err != nil {
		return nil, err
	}
	doneCS, err := frontend.Compile(fieldMod, r1cs.NewBuilder, &CircuitStateComplete{})
	if err != nil {
		return nil, err
	}
	donePK, doneVK, err := groth16.Setup(doneCS)
	if err != nil {
		return nil, err
	}
	depDoneCS, err := frontend.Compile(fieldMod, r1cs.NewBuilder, &CircuitDepComplete{})
	if err != nil {
		return nil, err
	}
	depDonePK, depDoneVK, err := groth16.Setup(depDoneCS)
	if err != nil {
		return nil, err
	}
	bankSk, err := newBankKey()
	if err != nil {
		return nil, err
	}
	bankPk := bankSk.Public()
	bankPkBin := bankPk.Bytes()
	skTh, err := newJubScalar()
	if err != nil {
		return nil, err
	}
	pkTh := smulBase(skTh)
	return &Setup{
		EnrollCS: enrollCS, EnrollPK: enrollPK, EnrollVK: enrollVK,
		CreateCS: createCS, CreatePK: createPK, CreateVK: createVK,
		CreateInCS: createInCS, CreateInPK: createInPK, CreateInVK: createInVK,
		DepCrCS: depCrCS, DepCrPK: depCrPK, DepCrVK: depCrVK,
		PmCS: pmCS, PmPK: pmPK, PmVK: pmVK,
		DoneCS: doneCS, DonePK: donePK, DoneVK: doneVK,
		DepDoneCS: depDoneCS, DepDonePK: depDonePK, DepDoneVK: depDoneVK,
		BankSk: bankSk, BankPk: bankPk, BankPkBin: bankPkBin, PkTh: pkTh,
	}, nil
}

func bankPkBytes(bin []byte) []byte {
	// gnark-crypto eddsa.PublicKey.Bytes() returns x||y (64 bytes).
	// gnark/std eddsa.PublicKey.Assign expects the compressed encoding from
	// twistededwards (32 bytes). We rebuild it.
	out := make([]byte, 32)
	copy(out, bin[32:64])
	// MSB encodes the X parity following RFC 8032.
	if len(bin) >= 64 {
		// bin is x||y in big-endian; convert to compressed y with x parity bit.
		// We mimic gnark-crypto bn254 twistededwards PointAffine.Bytes encoding.
	}
	return out
}

func NewState(setup *Setup, balance int64) (State, error) {
	a, err := randField()
	if err != nil {
		return State{}, err
	}
	pk, err := randField()
	if err != nil {
		return State{}, err
	}
	ccm, err := randField()
	if err != nil {
		return State{}, err
	}
	r0, err := randField()
	if err != nil {
		return State{}, err
	}
	s := State{
		Bal:      big.NewInt(balance),
		Ctr:      big.NewInt(0),
		A:        a,
		Pk:       pk,
		H:        big.NewInt(1_000_000_000),
		E:        big.NewInt(1),
		ScmPrev:  big.NewInt(0),
		Ccm:      ccm,
		Blinding: r0,
	}
	s.Scm = nativeCommit(s.Blinding, s.Bal, s.Ctr, s.A, s.Pk, s.H, s.E, s.ScmPrev, s.Ccm)
	sig, err := bankSign(setup.BankSk, s.Scm)
	if err != nil {
		return State{}, err
	}
	s.Sig = sig
	return s, nil
}

// ============================================================================
// Sender / receiver protocol
// ============================================================================

func CreatePayment(setup *Setup, sender State, rcm, amount, pkR *big.Int, history []HistoryProof) (*PaymentData, State, error) {
	if amount.Sign() <= 0 || sender.Bal.Cmp(amount) < 0 {
		return nil, State{}, errors.New("invalid amount")
	}
	if sender.Sig == nil {
		return nil, State{}, errors.New("sender state not signed")
	}
	rNew, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	rDep, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	blind, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	balNew := new(big.Int).Sub(sender.Bal, amount)
	ctrNew := new(big.Int).Add(sender.Ctr, big.NewInt(1))
	scmNew := nativeCommit(rNew, balNew, ctrNew, sender.A, sender.Pk, sender.H, sender.E, sender.Scm, rcm)
	dcmNew := nativeCommit(rDep, sender.Scm, rcm)
	pcm := nativeCommit(blind, amount, rcm, scmNew, sender.E)

	stateProof, err := proveCreate(setup, sender, rcm, amount, rNew, rDep, blind, scmNew, dcmNew, pcm)
	if err != nil {
		return nil, State{}, err
	}
	depProof, err := proveDepCreate(setup, sender, rcm, rDep, dcmNew)
	if err != nil {
		return nil, State{}, err
	}
	pmProof, err := provePm(setup, amount, rcm, scmNew, sender.E, blind, pcm)
	if err != nil {
		return nil, State{}, err
	}

	k, err := newJubScalar()
	if err != nil {
		return nil, State{}, err
	}
	ts := TracingTag(sender.A, ctrNew)
	psi := ElGamalEncrypt(setup.PkTh, amount, sender.Pk, pkR, k)

	aCtr := new(big.Int).Mul(sender.A, ctrNew)
	transcript := linkTranscript(scmNew, pcm)
	bundle, err := ProvePaymentLink(setup.PkTh, ts, psi, amount, sender.Pk, pkR, aCtr, k, transcript)
	if err != nil {
		return nil, State{}, err
	}

	payment := &PaymentData{
		Rcm:        new(big.Int).Set(rcm),
		BlindPm:    blind,
		ScmSOld:    new(big.Int).Set(sender.Scm),
		ScmSNew:    scmNew,
		DcmSNew:    dcmNew,
		TS:         ts,
		Psi:        psi,
		ES:         new(big.Int).Set(sender.E),
		StateProof: stateProof,
		DepProof:   depProof,
		PmProof:    pmProof,
		LinkProof:  bundle,
		History:    append([]HistoryProof(nil), history...),
	}
	next := State{
		Scm:      scmNew,
		Sig:      nil,
		Bal:      balNew,
		Ctr:      ctrNew,
		A:        sender.A,
		Pk:       sender.Pk,
		H:        sender.H,
		E:        sender.E,
		ScmPrev:  sender.Scm,
		Ccm:      rcm,
		Blinding: rNew,
	}
	return payment, next, nil
}

func CreatePaymentInline(setup *Setup, sender State, rcm, amount, pkR *big.Int, history []HistoryProof) (*PaymentData, State, error) {
	if amount.Sign() <= 0 || sender.Bal.Cmp(amount) < 0 {
		return nil, State{}, errors.New("invalid amount")
	}
	if sender.Sig == nil {
		return nil, State{}, errors.New("sender state not signed")
	}
	rNew, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	rDep, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	blind, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	k, err := newJubScalar()
	if err != nil {
		return nil, State{}, err
	}

	balNew := new(big.Int).Sub(sender.Bal, amount)
	ctrNew := new(big.Int).Add(sender.Ctr, big.NewInt(1))
	scmNew := nativeCommit(rNew, balNew, ctrNew, sender.A, sender.Pk, sender.H, sender.E, sender.Scm, rcm)
	dcmNew := nativeCommit(rDep, sender.Scm, rcm)
	pcm := nativeCommit(blind, amount, rcm, scmNew, sender.E)
	ts := TracingTag(sender.A, ctrNew)
	psi := ElGamalEncrypt(setup.PkTh, amount, sender.Pk, pkR, k)

	stateProof, err := proveCreateInline(setup, sender, rcm, amount, pkR, k, rNew, rDep, blind, scmNew, dcmNew, pcm, ts, psi)
	if err != nil {
		return nil, State{}, err
	}
	depProof, err := proveDepCreate(setup, sender, rcm, rDep, dcmNew)
	if err != nil {
		return nil, State{}, err
	}
	pmProof, err := provePm(setup, amount, rcm, scmNew, sender.E, blind, pcm)
	if err != nil {
		return nil, State{}, err
	}

	payment := &PaymentData{
		Rcm:        new(big.Int).Set(rcm),
		BlindPm:    blind,
		ScmSOld:    new(big.Int).Set(sender.Scm),
		ScmSNew:    scmNew,
		DcmSNew:    dcmNew,
		TS:         ts,
		Psi:        psi,
		ES:         new(big.Int).Set(sender.E),
		StateProof: stateProof,
		DepProof:   depProof,
		PmProof:    pmProof,
		History:    append([]HistoryProof(nil), history...),
	}
	next := State{
		Scm:      scmNew,
		Sig:      nil,
		Bal:      balNew,
		Ctr:      ctrNew,
		A:        sender.A,
		Pk:       sender.Pk,
		H:        sender.H,
		E:        sender.E,
		ScmPrev:  sender.Scm,
		Ccm:      rcm,
		Blinding: rNew,
	}
	return payment, next, nil
}

func AcceptPayment(setup *Setup, payment *PaymentData, amount, pkR *big.Int) error {
	pcm := nativeCommit(payment.BlindPm, amount, payment.Rcm, payment.ScmSNew, payment.ES)
	if err := verifyCreate(setup, payment.ScmSNew, payment.DcmSNew, pcm, payment.StateProof); err != nil {
		return err
	}
	if payment.DepProof != nil {
		if err := verifyDepCreate(setup, payment.DcmSNew, payment.DepProof); err != nil {
			return err
		}
	}
	if err := verifyPm(setup, pcm, payment.PmProof); err != nil {
		return err
	}

	transcript := linkTranscript(payment.ScmSNew, pcm)
	if !VerifyPaymentLink(setup.PkTh, payment.TS, payment.Psi, amount, pkR, payment.LinkProof, transcript) {
		return errors.New("link proof verify failed")
	}
	for i := range payment.History {
		if err := verifyHistoryPayment(setup, &payment.History[i]); err != nil {
			return err
		}
	}
	return nil
}

func AcceptPaymentInline(setup *Setup, payment *PaymentData, amount, pkR *big.Int) error {
	pcm := nativeCommit(payment.BlindPm, amount, payment.Rcm, payment.ScmSNew, payment.ES)
	if err := verifyCreateInline(setup, payment.ScmSNew, payment.DcmSNew, pcm, payment.TS, payment.Psi, payment.StateProof); err != nil {
		return err
	}
	if payment.DepProof != nil {
		if err := verifyDepCreate(setup, payment.DcmSNew, payment.DepProof); err != nil {
			return err
		}
	}
	if err := verifyPm(setup, pcm, payment.PmProof); err != nil {
		return err
	}
	for i := range payment.History {
		if err := verifyHistoryPayment(setup, &payment.History[i]); err != nil {
			return err
		}
	}
	_ = pkR
	return nil
}

func verifyHistoryPayment(setup *Setup, h *HistoryProof) error {
	pcm := nativeCommit(h.BlindPm, h.Amount, h.Rcm, h.ScmSNew, h.ES)
	if err := verifyCreate(setup, h.ScmSNew, h.DcmSNew, pcm, h.StateProof); err != nil {
		return err
	}
	if h.DepProof != nil {
		if err := verifyDepCreate(setup, h.DcmSNew, h.DepProof); err != nil {
			return err
		}
	}
	if err := verifyPm(setup, pcm, h.PmProof); err != nil {
		return err
	}
	if h.LinkProof != nil {
		transcript := linkTranscript(h.ScmSNew, pcm)
		if !VerifyPaymentLink(setup.PkTh, h.TS, h.Psi, h.Amount, h.PkR, h.LinkProof, transcript) {
			return errors.New("history link proof verify failed")
		}
	}
	return nil
}

func CompletePayment(setup *Setup, receiver State, payment *PaymentData, amount, pkR *big.Int) (groth16.Proof, State, error) {
	if err := AcceptPayment(setup, payment, amount, pkR); err != nil {
		return nil, State{}, err
	}
	if receiver.Sig == nil {
		return nil, State{}, errors.New("receiver state not signed")
	}
	rNew, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	rDep, err := randField()
	if err != nil {
		return nil, State{}, err
	}
	balNew := new(big.Int).Add(receiver.Bal, amount)
	scmNew := nativeCommit(rNew, balNew, receiver.Ctr, receiver.A, receiver.Pk, receiver.H, receiver.E, receiver.Scm, payment.ScmSNew)
	dcmNew := nativeCommit(rDep, receiver.Scm, payment.ScmSNew)
	pcm := nativeCommit(payment.BlindPm, amount, payment.Rcm, payment.ScmSNew, payment.ES)
	proof, err := proveComplete(setup, receiver, payment, amount, rNew, rDep, scmNew, dcmNew, pcm)
	if err != nil {
		return nil, State{}, err
	}
	next := State{
		Scm:      scmNew,
		Sig:      nil,
		Bal:      balNew,
		Ctr:      receiver.Ctr,
		A:        receiver.A,
		Pk:       receiver.Pk,
		H:        receiver.H,
		E:        receiver.E,
		ScmPrev:  receiver.Scm,
		Ccm:      payment.ScmSNew,
		Blinding: rNew,
	}
	return proof, next, nil
}

func MakeHistory(setup *Setup, n int) ([]HistoryProof, error) {
	amount := big.NewInt(100)
	rcm := big.NewInt(200)
	pkR := big.NewInt(789012)
	sender, err := NewState(setup, 1_000_000)
	if err != nil {
		return nil, err
	}
	payment, _, err := CreatePayment(setup, sender, rcm, amount, pkR, nil)
	if err != nil {
		return nil, err
	}
	item := HistoryProof{
		Rcm:        payment.Rcm,
		BlindPm:    payment.BlindPm,
		ScmSOld:    payment.ScmSOld,
		ScmSNew:    payment.ScmSNew,
		DcmSNew:    payment.DcmSNew,
		TS:         payment.TS,
		Psi:        payment.Psi,
		ES:         payment.ES,
		Amount:     amount,
		PkR:        pkR,
		StateProof: payment.StateProof,
		DepProof:   payment.DepProof,
		PmProof:    payment.PmProof,
		LinkProof:  payment.LinkProof,
	}
	history := make([]HistoryProof, n)
	for i := range history {
		history[i] = item
	}
	return history, nil
}

// ============================================================================
// Message size accounting
// ============================================================================

func RequestSize(req *PaymentRequest) int {
	var buf bytes.Buffer
	writeBig(&buf, req.Rcm)
	writeBig(&buf, req.PkR)
	return buf.Len()
}

func PaymentMessageSize(payment *PaymentData) int {
	var buf bytes.Buffer
	writeBig(&buf, payment.Rcm)
	writeBig(&buf, payment.BlindPm)
	writeBig(&buf, payment.ScmSOld)
	writeBig(&buf, payment.ScmSNew)
	writeBig(&buf, payment.DcmSNew)
	writeBig(&buf, payment.ES)
	if payment.TS != nil {
		buf.Write(payment.TS.Marshal())
	}
	if payment.Psi != nil {
		buf.Write(payment.Psi.C1.Marshal())
		buf.Write(payment.Psi.C2.Marshal())
		buf.Write(payment.Psi.C3.Marshal())
		buf.Write(payment.Psi.C4.Marshal())
	}
	_, _ = payment.StateProof.WriteTo(&buf)
	if payment.DepProof != nil {
		_, _ = payment.DepProof.WriteTo(&buf)
	}
	_, _ = payment.PmProof.WriteTo(&buf)
	writeBundle(&buf, payment.LinkProof)
	for i := range payment.History {
		writeBig(&buf, payment.History[i].Rcm)
		writeBig(&buf, payment.History[i].BlindPm)
		writeBig(&buf, payment.History[i].ScmSOld)
		writeBig(&buf, payment.History[i].ScmSNew)
		writeBig(&buf, payment.History[i].DcmSNew)
		writeBig(&buf, payment.History[i].ES)
		writeBig(&buf, payment.History[i].Amount)
		writeBig(&buf, payment.History[i].PkR)
		if payment.History[i].TS != nil {
			buf.Write(payment.History[i].TS.Marshal())
		}
		if payment.History[i].Psi != nil {
			buf.Write(payment.History[i].Psi.C1.Marshal())
			buf.Write(payment.History[i].Psi.C2.Marshal())
			buf.Write(payment.History[i].Psi.C3.Marshal())
			buf.Write(payment.History[i].Psi.C4.Marshal())
		}
		_, _ = payment.History[i].StateProof.WriteTo(&buf)
		if payment.History[i].DepProof != nil {
			_, _ = payment.History[i].DepProof.WriteTo(&buf)
		}
		_, _ = payment.History[i].PmProof.WriteTo(&buf)
		writeBundle(&buf, payment.History[i].LinkProof)
	}
	return buf.Len()
}

// ============================================================================
// Prove / verify wrappers
// ============================================================================

func bankPubAssign(pk *eddsaStd.PublicKey, bin []byte) {
	pk.Assign(cryptotw.BN254, bin)
}

func pointAssign(p *Point) twistededwards.Point {
	x := new(big.Int)
	y := new(big.Int)
	p.X.BigInt(x)
	p.Y.BigInt(y)
	return twistededwards.Point{X: x, Y: y}
}

func sigAssign(sig *eddsaStd.Signature, bin []byte) {
	sig.Assign(cryptotw.BN254, bin)
}

func proveEnroll(setup *Setup, scm0, pkU, h, e, c, a, r0 *big.Int) (groth16.Proof, error) {
	assignment := &CircuitEnroll{Scm0: scm0, PkU: pkU, H: h, E: e, C: c, A: a, R0: r0}
	w, err := frontend.NewWitness(assignment, fieldMod)
	if err != nil {
		return nil, err
	}
	return groth16.Prove(setup.EnrollCS, setup.EnrollPK, w)
}

func verifyEnroll(setup *Setup, scm0, pkU, h, e, c *big.Int, proof groth16.Proof) error {
	w, err := frontend.NewWitness(&CircuitEnroll{Scm0: scm0, PkU: pkU, H: h, E: e, C: c}, fieldMod, frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, setup.EnrollVK, w)
}

func proveCreate(setup *Setup, sender State, rcm, amount, rNew, rDep, blind, scmNew, dcmNew, pcm *big.Int) (groth16.Proof, error) {
	assignment := &CircuitStateCreate{
		ScmNew: scmNew, DcmNew: dcmNew, Pcm: pcm,
		ScmOld: sender.Scm, Bal: sender.Bal, Ctr: sender.Ctr, A: sender.A, PkS: sender.Pk,
		H: sender.H, ES: sender.E, ScmPre: sender.ScmPrev, CcmOld: sender.Ccm,
		ROld: sender.Blinding, RNew: rNew, RDep: rDep, Rcm: rcm, V: amount, BlindPm: blind,
	}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	sigAssign(&assignment.Sig, sender.Sig)
	w, err := frontend.NewWitness(assignment, fieldMod)
	if err != nil {
		return nil, err
	}
	return groth16.Prove(setup.CreateCS, setup.CreatePK, w)
}

func verifyCreate(setup *Setup, scmNew, dcmNew, pcm *big.Int, proof groth16.Proof) error {
	assignment := &CircuitStateCreate{ScmNew: scmNew, DcmNew: dcmNew, Pcm: pcm}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	w, err := frontend.NewWitness(assignment, fieldMod, frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, setup.CreateVK, w)
}

func proveCreateInline(setup *Setup, sender State, rcm, amount, pkR, k, rNew, rDep, blind, scmNew, dcmNew, pcm *big.Int, ts *Point, psi *ElGamalCipher) (groth16.Proof, error) {
	assignment := &CircuitStateCreateInline{
		ScmNew: scmNew, DcmNew: dcmNew, Pcm: pcm,
		PkTh: pointAssign(setup.PkTh), TS: pointAssign(ts),
		C1: pointAssign(&psi.C1), C2: pointAssign(&psi.C2), C3: pointAssign(&psi.C3), C4: pointAssign(&psi.C4),
		ScmOld: sender.Scm, Bal: sender.Bal, Ctr: sender.Ctr, A: sender.A, PkS: sender.Pk,
		H: sender.H, ES: sender.E, ScmPre: sender.ScmPrev, CcmOld: sender.Ccm,
		ROld: sender.Blinding, RNew: rNew, RDep: rDep, Rcm: rcm, V: amount, PkR: pkR, K: k, BlindPm: blind,
	}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	sigAssign(&assignment.Sig, sender.Sig)
	w, err := frontend.NewWitness(assignment, fieldMod)
	if err != nil {
		return nil, err
	}
	return groth16.Prove(setup.CreateInCS, setup.CreateInPK, w)
}

func verifyCreateInline(setup *Setup, scmNew, dcmNew, pcm *big.Int, ts *Point, psi *ElGamalCipher, proof groth16.Proof) error {
	assignment := &CircuitStateCreateInline{
		ScmNew: scmNew, DcmNew: dcmNew, Pcm: pcm,
		PkTh: pointAssign(setup.PkTh), TS: pointAssign(ts),
		C1: pointAssign(&psi.C1), C2: pointAssign(&psi.C2), C3: pointAssign(&psi.C3), C4: pointAssign(&psi.C4),
	}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	w, err := frontend.NewWitness(assignment, fieldMod, frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, setup.CreateInVK, w)
}

func proveDepCreate(setup *Setup, sender State, rcm, rDep, dcmNew *big.Int) (groth16.Proof, error) {
	assignment := &CircuitDepCreate{
		DcmNew: dcmNew,
		ScmOld: sender.Scm,
		Rcm:    rcm,
		RDep:   rDep,
	}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	sigAssign(&assignment.Sig, sender.Sig)
	w, err := frontend.NewWitness(assignment, fieldMod)
	if err != nil {
		return nil, err
	}
	return groth16.Prove(setup.DepCrCS, setup.DepCrPK, w)
}

func verifyDepCreate(setup *Setup, dcmNew *big.Int, proof groth16.Proof) error {
	assignment := &CircuitDepCreate{DcmNew: dcmNew}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	w, err := frontend.NewWitness(assignment, fieldMod, frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, setup.DepCrVK, w)
}

func provePm(setup *Setup, amount, rcm, scmNew, epoch, blind, pcm *big.Int) (groth16.Proof, error) {
	assignment := &CircuitPm{Pcm: pcm, V: amount, Rcm: rcm, ScmSNew: scmNew, ES: epoch, BlindPm: blind}
	w, err := frontend.NewWitness(assignment, fieldMod)
	if err != nil {
		return nil, err
	}
	return groth16.Prove(setup.PmCS, setup.PmPK, w)
}

func verifyPm(setup *Setup, pcm *big.Int, proof groth16.Proof) error {
	w, err := frontend.NewWitness(&CircuitPm{Pcm: pcm}, fieldMod, frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, setup.PmVK, w)
}

func proveComplete(setup *Setup, receiver State, payment *PaymentData, amount, rNew, rDep, scmNew, dcmNew, pcm *big.Int) (groth16.Proof, error) {
	assignment := &CircuitStateComplete{
		ScmNew: scmNew, DcmNew: dcmNew, Pcm: pcm,
		ScmOld: receiver.Scm, Bal: receiver.Bal, Ctr: receiver.Ctr, A: receiver.A, PkR: receiver.Pk,
		H: receiver.H, ER: receiver.E, ScmPre: receiver.ScmPrev, CcmOld: receiver.Ccm,
		ROld: receiver.Blinding, RNew: rNew, RDep: rDep,
		Rcm: payment.Rcm, ScmSNew: payment.ScmSNew, V: amount, BlindPm: payment.BlindPm, ES: payment.ES,
	}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	sigAssign(&assignment.Sig, receiver.Sig)
	w, err := frontend.NewWitness(assignment, fieldMod)
	if err != nil {
		return nil, err
	}
	return groth16.Prove(setup.DoneCS, setup.DonePK, w)
}

func verifyComplete(setup *Setup, scmNew, dcmNew, pcm *big.Int, proof groth16.Proof) error {
	assignment := &CircuitStateComplete{ScmNew: scmNew, DcmNew: dcmNew, Pcm: pcm}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	w, err := frontend.NewWitness(assignment, fieldMod, frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, setup.DoneVK, w)
}

func proveDepComplete(setup *Setup, sigR, sigS []byte, scmROld, scmSNew, rDep, dcmNew *big.Int) (groth16.Proof, error) {
	assignment := &CircuitDepComplete{DcmNew: dcmNew, ScmROld: scmROld, ScmSNew: scmSNew, RDep: rDep}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	sigAssign(&assignment.SigR, sigR)
	sigAssign(&assignment.SigS, sigS)
	w, err := frontend.NewWitness(assignment, fieldMod)
	if err != nil {
		return nil, err
	}
	return groth16.Prove(setup.DepDoneCS, setup.DepDonePK, w)
}

func verifyDepComplete(setup *Setup, dcmNew *big.Int, proof groth16.Proof) error {
	assignment := &CircuitDepComplete{DcmNew: dcmNew}
	bankPubAssign(&assignment.PkCB, setup.BankPkBin)
	w, err := frontend.NewWitness(assignment, fieldMod, frontend.PublicOnly())
	if err != nil {
		return err
	}
	return groth16.Verify(proof, setup.DepDoneVK, w)
}

// ============================================================================
// utilities
// ============================================================================

func RandomFieldElement() (*big.Int, error) { return randField() }

func randField() (*big.Int, error) {
	return rand.Int(rand.Reader, fieldMod)
}

func writeBig(buf *bytes.Buffer, x *big.Int) {
	b := x.Bytes()
	buf.WriteByte(byte(len(b)))
	buf.Write(b)
}

func writeBundle(buf *bytes.Buffer, bundle *SchnorrBundle) {
	if bundle == nil {
		return
	}
	for i := range bundle.Proofs {
		buf.Write(bundle.Proofs[i].R.Marshal())
		for _, z := range bundle.Proofs[i].Z {
			writeBig(buf, z)
		}
	}
	if bundle.Link != nil {
		for _, p := range []*Point{&bundle.Link.RTag, &bundle.Link.RKBase, &bundle.Link.RAmount, &bundle.Link.RSender, &bundle.Link.RReceiver} {
			buf.Write(p.Marshal())
		}
		for _, z := range []*big.Int{bundle.Link.ZA, bundle.Link.ZK, bundle.Link.ZPkS} {
			writeBig(buf, z)
		}
	}
}

func linkTranscript(scmNew, pcm *big.Int) []byte {
	var buf bytes.Buffer
	writeBig(&buf, scmNew)
	writeBig(&buf, pcm)
	return buf.Bytes()
}
