package payaudit

import (
	"crypto/rand"
	"crypto/sha256"
	"errors"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	tedbn254 "github.com/consensys/gnark-crypto/ecc/bn254/twistededwards"
	cryptotw "github.com/consensys/gnark-crypto/ecc/twistededwards"
	"github.com/consensys/gnark-crypto/hash"
	"github.com/consensys/gnark-crypto/signature"
	eddsaCrypto "github.com/consensys/gnark-crypto/signature/eddsa"
)

type Point = tedbn254.PointAffine

var (
	fieldMod = ecc.BN254.ScalarField()

	jubCurve = tedbn254.GetEdwardsCurve()
	jubBase  = jubCurve.Base
	jubOrder = new(big.Int).Set(&jubCurve.Order)
)

func nativeCommit(values ...*big.Int) *big.Int {
	h := hash.MIMC_BN254.New()
	var b [32]byte
	for _, v := range values {
		x := new(big.Int).Mod(v, fieldMod)
		x.FillBytes(b[:])
		h.Write(b[:])
	}
	out := h.Sum(nil)
	return new(big.Int).SetBytes(out)
}

func msgBytes(v *big.Int) []byte {
	var b [32]byte
	new(big.Int).Mod(v, fieldMod).FillBytes(b[:])
	return b[:]
}

func newBankKey() (signature.Signer, error) {
	return eddsaCrypto.New(cryptotw.BN254, rand.Reader)
}

func bankSign(sk signature.Signer, msg *big.Int) ([]byte, error) {
	return sk.Sign(msgBytes(msg), hash.MIMC_BN254.New())
}

func bankVerify(pk signature.PublicKey, sig []byte, msg *big.Int) (bool, error) {
	return pk.Verify(sig, msgBytes(msg), hash.MIMC_BN254.New())
}

func smul(p *Point, s *big.Int) *Point {
	var r Point
	x := new(big.Int).Mod(s, jubOrder)
	r.ScalarMultiplication(p, x)
	return &r
}

func smulBase(s *big.Int) *Point {
	return smul(&jubBase, s)
}

func padd(a, b *Point) *Point {
	var r Point
	r.Add(a, b)
	return &r
}

func newJubScalar() (*big.Int, error) {
	return rand.Int(rand.Reader, jubOrder)
}

type ElGamalCipher struct {
	C1, C2, C3, C4 Point
}

func ElGamalEncrypt(pkTh *Point, v, pkS, pkR, k *big.Int) *ElGamalCipher {
	pkThK := smul(pkTh, k)
	return &ElGamalCipher{
		C1: *smulBase(k),
		C2: *padd(smulBase(v), pkThK),
		C3: *padd(smulBase(pkS), pkThK),
		C4: *padd(smulBase(pkR), pkThK),
	}
}

func TracingTag(a, ctr *big.Int) *Point {
	s := new(big.Int).Mul(a, ctr)
	s.Mod(s, jubOrder)
	return smulBase(s)
}

type Statement struct {
	Bases  []*Point
	Result *Point
}

type LinearProof struct {
	R Point
	Z []*big.Int
}

type PaymentLinkProof struct {
	RTag, RKBase, RAmount, RSender, RReceiver Point
	ZA, ZK, ZPkS                              *big.Int
}

type SchnorrBundle struct {
	Proofs []LinearProof
	Link   *PaymentLinkProof
}

func sumScalarMul(bases []*Point, scalars []*big.Int) *Point {
	var acc Point
	for i, B := range bases {
		zB := smul(B, scalars[i])
		if i == 0 {
			acc = *zB
		} else {
			acc = *padd(&acc, zB)
		}
	}
	return &acc
}

func challenge(stmts []Statement, Rs []*Point, transcript []byte) *big.Int {
	h := sha256.New()
	h.Write(transcript)
	for i, st := range stmts {
		for _, B := range st.Bases {
			h.Write(B.Marshal())
		}
		h.Write(st.Result.Marshal())
		h.Write(Rs[i].Marshal())
	}
	c := new(big.Int).SetBytes(h.Sum(nil))
	c.Mod(c, jubOrder)
	return c
}

func ProveBundle(stmts []Statement, scalars [][]*big.Int, transcript []byte) (*SchnorrBundle, error) {
	if len(stmts) != len(scalars) {
		return nil, errors.New("schnorr: length mismatch")
	}
	Rs := make([]*Point, len(stmts))
	rs := make([][]*big.Int, len(stmts))
	for i, st := range stmts {
		if len(st.Bases) != len(scalars[i]) {
			return nil, errors.New("schnorr: scalar count mismatch")
		}
		row := make([]*big.Int, len(st.Bases))
		for j := range st.Bases {
			r, err := newJubScalar()
			if err != nil {
				return nil, err
			}
			row[j] = r
		}
		rs[i] = row
		Rs[i] = sumScalarMul(st.Bases, row)
	}
	c := challenge(stmts, Rs, transcript)
	proofs := make([]LinearProof, len(stmts))
	for i, st := range stmts {
		zs := make([]*big.Int, len(st.Bases))
		for j := range st.Bases {
			z := new(big.Int).Mul(c, scalars[i][j])
			z.Add(z, rs[i][j])
			z.Mod(z, jubOrder)
			zs[j] = z
		}
		proofs[i] = LinearProof{R: *Rs[i], Z: zs}
	}
	return &SchnorrBundle{Proofs: proofs}, nil
}

func VerifyBundle(stmts []Statement, bundle *SchnorrBundle, transcript []byte) bool {
	if bundle == nil || len(stmts) != len(bundle.Proofs) {
		return false
	}
	Rs := make([]*Point, len(stmts))
	for i := range bundle.Proofs {
		Rs[i] = &bundle.Proofs[i].R
	}
	c := challenge(stmts, Rs, transcript)
	for i, st := range stmts {
		lhs := sumScalarMul(st.Bases, bundle.Proofs[i].Z)
		rhs := padd(&bundle.Proofs[i].R, smul(st.Result, c))
		if !lhs.Equal(rhs) {
			return false
		}
	}
	return true
}

func pointMinusBaseScalar(p *Point, s *big.Int) *Point {
	neg := new(big.Int).Neg(s)
	return padd(p, smulBase(neg))
}

func paymentLinkChallenge(pkTh, ts *Point, psi *ElGamalCipher, amount, pkR *big.Int, proof *PaymentLinkProof, transcript []byte) *big.Int {
	c2 := pointMinusBaseScalar(&psi.C2, amount)
	c4 := pointMinusBaseScalar(&psi.C4, pkR)
	h := sha256.New()
	h.Write(transcript)
	for _, p := range []*Point{&jubBase, pkTh, ts, &psi.C1, c2, &psi.C3, c4, &proof.RTag, &proof.RKBase, &proof.RAmount, &proof.RSender, &proof.RReceiver} {
		h.Write(p.Marshal())
	}
	c := new(big.Int).SetBytes(h.Sum(nil))
	c.Mod(c, jubOrder)
	return c
}

func ProvePaymentLink(pkTh, ts *Point, psi *ElGamalCipher, amount, pkS, pkR, aCtr, k *big.Int, transcript []byte) (*SchnorrBundle, error) {
	rA, err := newJubScalar()
	if err != nil {
		return nil, err
	}
	rK, err := newJubScalar()
	if err != nil {
		return nil, err
	}
	rPkS, err := newJubScalar()
	if err != nil {
		return nil, err
	}
	proof := &PaymentLinkProof{
		RTag:      *smulBase(rA),
		RKBase:    *smulBase(rK),
		RAmount:   *smul(pkTh, rK),
		RSender:   *padd(smulBase(rPkS), smul(pkTh, rK)),
		RReceiver: *smul(pkTh, rK),
	}
	c := paymentLinkChallenge(pkTh, ts, psi, amount, pkR, proof, transcript)
	proof.ZA = new(big.Int).Mod(new(big.Int).Add(rA, new(big.Int).Mul(c, aCtr)), jubOrder)
	proof.ZK = new(big.Int).Mod(new(big.Int).Add(rK, new(big.Int).Mul(c, k)), jubOrder)
	proof.ZPkS = new(big.Int).Mod(new(big.Int).Add(rPkS, new(big.Int).Mul(c, pkS)), jubOrder)
	return &SchnorrBundle{Link: proof}, nil
}

func VerifyPaymentLink(pkTh, ts *Point, psi *ElGamalCipher, amount, pkR *big.Int, bundle *SchnorrBundle, transcript []byte) bool {
	if bundle == nil || bundle.Link == nil || pkTh == nil || ts == nil || psi == nil {
		return false
	}
	proof := bundle.Link
	c := paymentLinkChallenge(pkTh, ts, psi, amount, pkR, proof, transcript)
	c2 := pointMinusBaseScalar(&psi.C2, amount)
	c4 := pointMinusBaseScalar(&psi.C4, pkR)
	checks := []struct {
		lhs *Point
		rhs *Point
	}{
		{smulBase(proof.ZA), padd(&proof.RTag, smul(ts, c))},
		{smulBase(proof.ZK), padd(&proof.RKBase, smul(&psi.C1, c))},
		{smul(pkTh, proof.ZK), padd(&proof.RAmount, smul(c2, c))},
		{padd(smulBase(proof.ZPkS), smul(pkTh, proof.ZK)), padd(&proof.RSender, smul(&psi.C3, c))},
		{smul(pkTh, proof.ZK), padd(&proof.RReceiver, smul(c4, c))},
	}
	for _, check := range checks {
		if !check.lhs.Equal(check.rhs) {
			return false
		}
	}
	return true
}

func bundleSize(b *SchnorrBundle) int {
	if b == nil {
		return 0
	}
	n := 0
	for i := range b.Proofs {
		bx := b.Proofs[i].R.Marshal()
		n += len(bx)
		for _, z := range b.Proofs[i].Z {
			n += 1 + len(z.Bytes())
		}
	}
	if b.Link != nil {
		for _, p := range []*Point{&b.Link.RTag, &b.Link.RKBase, &b.Link.RAmount, &b.Link.RSender, &b.Link.RReceiver} {
			n += len(p.Marshal())
		}
		for _, z := range []*big.Int{b.Link.ZA, b.Link.ZK, b.Link.ZPkS} {
			n += 1 + len(z.Bytes())
		}
	}
	return n
}

func pointSize(p *Point) int {
	if p == nil {
		return 0
	}
	bx := p.Marshal()
	return len(bx)
}

func cipherSize(c *ElGamalCipher) int {
	if c == nil {
		return 0
	}
	return pointSize(&c.C1) + pointSize(&c.C2) + pointSize(&c.C3) + pointSize(&c.C4)
}
