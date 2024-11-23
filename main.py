from math import prod
from typing import Optional, Tuple, List
import unittest
from dataclasses import dataclass
import random
from hashlib import sha256

# Crypto/math primitives


def gcd(a: int, b: int) -> Tuple[int, int, int]:
    """
    Returns (gcd, x, y) s.t. a * x + b * y == gcd
    This function implements the extended Euclidean
    algorithm and runs in O(log b) in the worst case.
    """
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return old_r, old_s, old_t


def inv(a: int, p: int) -> int:
    """Find the modular multiplicative inverse using extended euclidean algorithm."""
    _divisor, x, _y = gcd(a, p)
    return x % p


def rand_secret() -> int:
    return random.randrange(1, generator.n)


@dataclass(frozen=True)
class Curve:
    a: int
    b: int
    p: int

    def eval(self, x: int) -> int:
        return (x**3 + self.a * x + self.b) % self.p

    def check(self, x: int, y: int) -> bool:
        """Check if the point is on the curve."""
        return (y**2) % self.p == self.eval(x)


secp256k1 = Curve(
    a=0x0000000000000000000000000000000000000000000000000000000000000000,  # a = 0
    b=0x0000000000000000000000000000000000000000000000000000000000000007,  # b = 7
    p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
)


@dataclass(frozen=True)
class Point:
    curve: Curve
    x: int
    y: int

    @staticmethod
    def inf() -> "Point":
        return Point(secp256k1, 0, 0)

    def __add__(self, other: "Point") -> "Point":
        # Edge cases
        # P + 0 = 0 + P
        if self == Point.inf():
            return other
        if other == Point.inf():
            return self
        # P + (-P) = 0
        if self.x == other.x and self.y != other.y:
            return Point.inf()

        # Find the slope of the line between the two current points.
        if self.x == other.x:
            # Derivative of the curve at this point, i.e. tangent line = 3x^2/2y
            # We cannot do rise over run because the denominator is 0
            m = (3 * (self.x**2) + self.curve.a) * inv(2 * self.y, self.curve.p)
        else:
            # Slope of the line connecting the two points, i.e. rise over run
            m = (self.y - other.y) * inv(self.x - other.x, self.curve.p)

        # To find the new point, we find the intersection of the line with the curve.
        # I.e. the solution to the set of equations: y^2=x^3+7 and y=mx+b
        # This results in the following: x=m^2-x_0-x_1 and y=m*(x-x_0)+y_0
        # And we take the negative of y because that's how elliptic curve addition
        # is defined.
        x = (m**2 - self.x - other.x) % self.curve.p
        y = (-(m * (x - self.x) + self.y)) % self.curve.p
        return Point(self.curve, x, y)

    def __mul__(self, k: int) -> "Point":
        # Multiplication is just adding over and over like in normal arithmetic.
        # This is just a more efficient way of doing multiplication with
        # large numbers, i.e. double and add
        assert isinstance(k, int) and k >= 0
        result = Point.inf()
        append = self
        while k > 0:
            if k & 1:
                result += append
            append += append
            k >>= 1
        return result

    def to_bytes(self) -> bytes:
        return bytes([2 if self.y % 2 == 0 else 3]) + int.to_bytes(
            self.x, 32, "big"
        )  # big endian


G = Point(
    secp256k1,
    x=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    y=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
)


@dataclass(frozen=True)
class Generator:
    G: Point
    n: int


generator = Generator(
    G=G,
    # the order of G is known and can be mathematically derived
    n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
)

# Basic schnorr signature


@dataclass
class Signature:
    r: Point
    s: int


def sign_schnorr(
    sk: int, msg: bytes, k: Optional[int] = None, r: Optional[Point] = None
) -> Signature:
    """Returns (s, e) where
    e = H(r || msg)
    s = k - sk * e

    Args:
        sk: secret key
        msg: the message to sign
        k: a random nonce
        r: the public nonce (either G * k or a shared nonce)
    """
    if k is None:
        assert r is None
        k = rand_secret()
    if r is None:
        r = G * k
    e_bytes = sha256(r.to_bytes() + msg).digest()
    e = int.from_bytes(e_bytes, "big")
    s = (k - sk * e) % generator.n
    return Signature(r, s)


def verify_schnorr(sig: Signature, pk: Point, msg: bytes) -> bool:
    """Returns whether the signature (r, s) is valid with the
    provided public key (pk) for the message, i.e.
    e = H(r || msg)
    G * s + pk * e == r
    """
    # Spelled out:
    # G * s + pk * e
    # = G * (k - sk * e) + (G * sk) * e
    # = G * k = r
    e_bytes = sha256(sig.r.to_bytes() + msg).digest()
    e = int.from_bytes(e_bytes, "big")
    return G * sig.s + pk * e == sig.r


def sk_from_nonce_reuse(
    msg1: bytes, sig1: Signature, msg2: bytes, sig2: Signature
) -> int:
    """Solves for the secret key given two signatures that reuse a nonce."""
    # Spelled out:
    # sig1.s = k - sk * e1
    # sig2.s = k - sk * e2
    # sig1.s - sig2.s = (k - sk * e1) - (k - sk * e2)
    # = sk * e2 - sk * e1
    # = sk * (e2 - e1)
    # sk = (sig1.s - sig2.s) / (e2 - e1)
    r = sig1.r
    e1_bytes = sha256(r.to_bytes() + msg1).digest()
    e1 = int.from_bytes(e1_bytes, "big")
    e2_bytes = sha256(r.to_bytes() + msg2).digest()
    e2 = int.from_bytes(e2_bytes, "big")
    sk = (sig1.s - sig2.s) * inv(e2 - e1, generator.n) % generator.n
    return sk


# Threshold signing


def eval_polynomial(coeffs: List[int], x: int) -> int:
    """Evaluates a polynomial of degree len(coeffs)-1 at x.

    Example:
    coeffs = [1, 2, 3]
    eval_polynomial(coeffs, x) = 1x^2 + 2x^1 + 3x^0
    """
    return (
        sum(c * x**i for i, c in zip(reversed(range(len(coeffs))), coeffs))
        % generator.n
    )


class ThresholdSigner:
    def __init__(self, t: int, sk: int = rand_secret()):
        self.t = t
        self.sk = sk
        self.pk = G * sk
        # t - 1 because the last coefficient is our secret key
        self.coeffs = [rand_secret() for _ in range(t - 1)] + [sk]
        self.idx: Optional[int] = None
        self.share: Optional[int] = None

    def compute_partial_share(self, idx: int) -> int:
        return eval_polynomial(self.coeffs, idx)

    def set_share(self, idx: int, partial_shares: List[int]):
        self.idx = idx
        self.share = (
            self.compute_partial_share(self.idx) + sum(partial_shares)
        ) % generator.n

    # Post DKG

    def compute_lambda(self, other_idxs: List[int]) -> int:
        assert self.idx is not None and self.share is not None
        # Lagrange interpolation: https://en.wikipedia.org/wiki/Lagrange_polynomial
        return (
            prod(
                ((0 - other_idxs[i]) * inv(self.idx - other_idxs[i], generator.n))
                for i in range(len(other_idxs))
            )
            * self.share
            % generator.n
        )


def get_signer_idxs(signers: List[ThresholdSigner]) -> List[int]:
    return [
        idx
        for _, idx in sorted(
            zip(signers, range(1, len(signers) + 1)), key=lambda x: x[0].pk.to_bytes()
        )
    ]


def distribute_shares(signers: List[ThresholdSigner]) -> None:
    idxs = get_signer_idxs(signers)
    for idx, signer in zip(idxs, signers):
        partial_shares = [
            other_signer.compute_partial_share(idx)
            for other_signer in signers
            if other_signer != signer
        ]
        signer.set_share(idx, partial_shares)


def threshold_sign(
    signers: List[ThresholdSigner], signer_idxs: List[int], msg: bytes
) -> Signature:
    assert len(signers) == len(signer_idxs)
    # TODO: do we need to tweak with our pubkey somewhere?
    nonces = [rand_secret() for _ in signers]
    agg_nonce = sum((G * k for k in nonces), Point.inf())

    partial_signatures: List[Signature] = []
    for idx, signer, nonce in zip(signer_idxs, signers, nonces):
        other_signer_idxs = [i for i in signer_idxs if i != idx]
        lambda_curr = signer.compute_lambda(other_signer_idxs)
        partial_signature = sign_schnorr(lambda_curr, msg, nonce, agg_nonce)
        partial_signatures.append(partial_signature)
    sig_agg = Signature(
        agg_nonce, sum((sig.s for sig in partial_signatures)) % generator.n
    )
    return sig_agg


class TestThresholdSigning(unittest.TestCase):
    def test_curve(self):
        assert secp256k1.check(G.x, G.y)
        g2 = G + G
        assert secp256k1.check(g2.x, g2.y)
        assert G * 2 * 3 == G * 6
        sk = rand_secret()
        sk2 = rand_secret()
        assert sk + sk2 == sk2 + sk
        assert G * sk + G * sk2 == G * (sk + sk2)

    def test_sign_verify(self):
        sk = rand_secret()
        pk = G * sk
        msg = b"Which cryptography struggled with sleep apnea?"
        sig = sign_schnorr(sk, msg)
        assert verify_schnorr(sig, pk, msg)

    def test_nonce_reuse(self):
        # If you reuse the nonce, an attacker can solve for your secret key
        sk = rand_secret()
        pk = G * sk
        k1 = rand_secret()
        msg1 = b"Hello"
        sig1 = sign_schnorr(sk, msg1, k1)
        assert verify_schnorr(sig1, pk, msg1)
        msg2 = b"Goodbye"
        sig2 = sign_schnorr(sk, msg2, k1)
        assert verify_schnorr(sig2, pk, msg2)
        solved_sk = sk_from_nonce_reuse(msg1, sig1, msg2, sig2)
        assert solved_sk == sk
        # If you don't reuse the nonce, it doesn't work
        k2 = rand_secret()
        sig3 = sign_schnorr(sk, msg2, k2)
        assert verify_schnorr(sig3, pk, msg2)
        solved_sk = sk_from_nonce_reuse(msg1, sig1, msg2, sig3)
        assert solved_sk != sk

    def test_schnorr_multisig(self):
        # Basic 2-of-2 signing
        sk1 = rand_secret()
        sk2 = rand_secret()
        pk1 = G * sk1
        pk2 = G * sk2
        sk_agg = (sk1 + sk2) % generator.n
        pk_agg = pk1 + pk2
        assert pk_agg == G * sk_agg

        # Signing
        # e = H((k1 + k2) || msg)
        # s1 = k1 + sk1 * e
        # s2 = k2 + sk2 * e
        # s3 = (k1 + k2) + (sk1 + sk2) * e
        msg = b"Hello"
        k1 = rand_secret()
        k2 = rand_secret()
        r1 = G * k1
        r2 = G * k2
        r_agg = r1 + r2
        sig1 = sign_schnorr(sk1, msg, k1, r_agg)
        sig2 = sign_schnorr(sk2, msg, k2, r_agg)
        sig_agg = Signature(r_agg, sig1.s + sig2.s)
        assert verify_schnorr(sig_agg, pk_agg, msg)

    def test_threshold_signing_manual(self):
        # 2/3 threshold signing
        sk1 = rand_secret()
        sk2 = rand_secret()
        sk3 = rand_secret()
        pk1 = G * sk1
        pk2 = G * sk2
        pk3 = G * sk3
        pk_agg = pk1 + pk2 + pk3
        m1 = rand_secret()
        m2 = rand_secret()
        m3 = rand_secret()
        line1 = lambda x: (m1 * x + sk1) % generator.n
        line2 = lambda x: (m2 * x + sk2) % generator.n
        line3 = lambda x: (m3 * x + sk3) % generator.n
        idx1 = 1
        idx2 = 2
        idx3 = 3
        y11 = line1(idx1)
        y12 = line1(idx2)
        y13 = line1(idx3)
        y21 = line2(idx1)
        y22 = line2(idx2)
        y23 = line2(idx3)
        y31 = line3(idx1)
        y32 = line3(idx2)
        y33 = line3(idx3)
        share1 = y11 + y21 + y31
        share2 = y12 + y22 + y32
        share3 = y13 + y23 + y33

        # Rederiving the shared secret from all shares
        # Lagrange interpolation: https://en.wikipedia.org/wiki/Lagrange_polynomial
        lambda1 = (
            (
                (0 - idx2)
                * inv(idx1 - idx2, generator.n)
                * (0 - idx3)
                * inv(idx1 - idx3, generator.n)
            )
            * share1
            % generator.n
        )
        lambda2 = (
            (
                (0 - idx1)
                * inv(idx2 - idx1, generator.n)
                * (0 - idx3)
                * inv(idx2 - idx3, generator.n)
            )
            * share2
            % generator.n
        )
        lambda3 = (
            (
                (0 - idx1)
                * inv(idx3 - idx1, generator.n)
                * (0 - idx2)
                * inv(idx3 - idx2, generator.n)
            )
            * share3
            % generator.n
        )
        sk_agg = (lambda1 + lambda2 + lambda3) % generator.n
        assert sk_agg == (sk1 + sk2 + sk3) % generator.n

        # Rederiving the shared secret from only two shares
        lambda12 = (0 - idx2) * inv(idx1 - idx2, generator.n) * share1 % generator.n
        lambda21 = (0 - idx1) * inv(idx2 - idx1, generator.n) * share2 % generator.n
        sk_agg = (lambda12 + lambda21) % generator.n
        assert sk_agg == (sk1 + sk2 + sk3) % generator.n

        # Signing for the aggregate key with two shares
        msg = b"Hello"
        k1 = rand_secret()
        k2 = rand_secret()
        r1 = G * k1
        r2 = G * k2
        r_agg = r1 + r2
        sig1 = sign_schnorr(lambda12, msg, k1, r_agg)
        sig2 = sign_schnorr(lambda21, msg, k2, r_agg)
        sig_agg = Signature(r_agg, sig1.s + sig2.s)
        assert verify_schnorr(sig_agg, pk_agg, msg)

    def test_threshold_signing_two(self):
        # 2/3 threshold signing
        t = 2
        signer1 = ThresholdSigner(t)
        signer2 = ThresholdSigner(t)
        signer3 = ThresholdSigner(t)
        signers = [signer1, signer2, signer3]

        # Naive DKG
        idxs = get_signer_idxs(signers)
        distribute_shares(signers)

        # Sign with any two of the three signers
        msg = b"Why do cryptographers love bagels?"
        pk_agg = sum((signer.pk for signer in signers), Point.inf())
        sig_agg = threshold_sign([signer1, signer2], [idxs[0], idxs[1]], msg)
        assert verify_schnorr(sig_agg, pk_agg, msg)
        sig_agg = threshold_sign([signer2, signer3], [idxs[1], idxs[2]], msg)
        assert verify_schnorr(sig_agg, pk_agg, msg)
        sig_agg = threshold_sign([signer1, signer3], [idxs[0], idxs[2]], msg)
        assert verify_schnorr(sig_agg, pk_agg, msg)

    def test_threshold_signing_many(self):
        t = random.randrange(3, 10)
        n = random.randrange(t, 15)
        signers = [ThresholdSigner(t) for _ in range(n)]
        idxs = get_signer_idxs(signers)
        distribute_shares(signers)

        msg = b"Okay I ran out of original jokes"
        pk_agg = sum((signer.pk for signer in signers), Point.inf())
        sig_agg = threshold_sign(signers[:t], idxs[:t], msg)
        assert verify_schnorr(sig_agg, pk_agg, msg)

    def test_adaptor_signatures(self):
        # Alice
        sk1 = rand_secret()
        pk1 = G * sk1
        t = rand_secret()  # hidden value
        m = b"Hello"
        m2 = b"Goodbye"

        k = rand_secret()
        sig = sign_schnorr(sk1, m, k + t, G * k + G * t)
        # sig = k + t - H(G * k + G * t || m) * sk1
        # sig' = k - H(G * k + G * t || m) * sk1
        # G * sig' = G * k - pk1 * (G * k + G * t || m)
        sig_prime = (sig.s - t) % generator.n
        adaptor = (sig_prime, G * k, G * t)

        # Bob
        assert (
            G * adaptor[0]
            + pk1
            * int.from_bytes(
                sha256((adaptor[1] + adaptor[2]).to_bytes() + m).digest(), "big"
            )
            == adaptor[1]
        )
        sk2 = rand_secret()
        pk2 = G * sk2
        k2 = rand_secret()
        sig2 = sign_schnorr(sk2, m2, k2, G * k2 + adaptor[2])
        # sig2 = k2 - H(G * k2 + G * t || m) * sk2
        adaptor2 = (sig2.s, G * k2, adaptor[2])

        # Alice
        sig3 = Signature(adaptor2[1] + adaptor2[2], (sig2.s + t) % generator.n)
        assert verify_schnorr(sig3, pk2, m2)
        # Broadcasts

        # Bob solves for t, and gets Alice's signature from earlier adaptor using t
        t_solved = (sig3.s - sig2.s) % generator.n
        assert t == t_solved
        sig4 = Signature(adaptor[1] + adaptor[2], (adaptor[0] + t) % generator.n)
        assert verify_schnorr(sig4, pk1, m)


if __name__ == "__main__":
    unittest.main()
