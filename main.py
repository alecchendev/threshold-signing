from typing import Tuple
import unittest
from dataclasses import dataclass
import random
from hashlib import sha256

# Goal: demonstrate threshold signing end to end in the simplest way possible
# 1. DKG
# 2. Signing
# 3. Verification?


def gcd(a: int, b: int) -> Tuple[int, int, int]:
    """
    Returns (gcd, x, y) s.t. a * x + b * y == gcd
    This function implements the extended Euclidean
    algorithm and runs in O(log b) in the worst case,
    taken from Wikipedia.

    Source: Andrej Karpathy
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
    """Find the inverse using extended euclidean algorithm."""
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
        # More efficient way of doing multiplication with large numbers,
        # i.e. double and add
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


@dataclass
class Signature:
    r: Point
    s: int


def sign(sk: int, msg: bytes) -> Signature:
    """Returns (s, e) where
    r = k * G
    e = H(r || msg)
    s = k - sk * e
    """
    k = rand_secret()
    r = G * k
    e_bytes = sha256(r.to_bytes() + msg).digest()
    e = int.from_bytes(e_bytes, "big")
    s = (k - sk * e) % generator.n
    return Signature(r, s)


def sign_with_nonce(k: int, sk: int, msg: bytes) -> Signature:
    """Returns (s, e) where
    r = k * G
    e = H(r || msg)
    s = k - sk * e
    """
    r = G * k
    e_bytes = sha256(r.to_bytes() + msg).digest()
    e = int.from_bytes(e_bytes, "big")
    s = (k - sk * e) % generator.n
    return Signature(r, s)


def sign_with_nonce_and_agg_nonce(
    k: int, r_agg: Point, sk: int, msg: bytes
) -> Signature:
    """Returns (s, e) where
    r = k * G
    e = H(r || msg)
    s = k - sk * e
    """
    e_bytes = sha256(r_agg.to_bytes() + msg).digest()
    e = int.from_bytes(e_bytes, "big")
    s = (k - sk * e) % generator.n
    return Signature(r_agg, s)


def verify(sig: Signature, pk: Point, msg: bytes) -> bool:
    """Returns whether the signature (r, s) is valid with the
    provided public key (pk) for the message, i.e.
    e = H(r || msg)
    G * s + pk * e == r
    """
    # Spelled out:
    # G * s = G * (k - sk * e)
    # pk * e = G * (sk * e)
    # G * s + pk * e = G * (k - sk * e) + G * (sk * e)
    # = G * k = r
    e_bytes = sha256(sig.r.to_bytes() + msg).digest()
    e = int.from_bytes(e_bytes, "big")
    return G * sig.s + pk * e == sig.r


def sk_from_nonce_reuse(
    msg1: bytes, sig1: Signature, msg2: bytes, sig2: Signature
) -> int:
    assert sig1.r == sig2.r
    r = sig1.r
    e1_bytes = sha256(r.to_bytes() + msg1).digest()
    e1 = int.from_bytes(e1_bytes, "big")
    e2_bytes = sha256(r.to_bytes() + msg2).digest()
    e2 = int.from_bytes(e2_bytes, "big")
    # sig1.s = k - sk * e1
    # sig2.s = k - sk * e2
    # sig1.s - sig2.s = (k - sk * e1) - (k - sk * e2)
    # = sk * e2 - sk * e1
    # = sk * (e2 - e1)
    # sk = (sig1.s - sig2.s) / (e2 - e1)
    sk = (sig1.s - sig2.s) * inv(e2 - e1, generator.n) % generator.n
    return sk


class TestThresholdSigning(unittest.TestCase):
    def test_curve(self):
        assert secp256k1.check(G.x, G.y)
        assert G * 2 * 3 == G * 6
        sk = rand_secret()
        sk2 = rand_secret()
        assert sk + sk2 == sk2 + sk
        assert G * sk + G * sk2 == G * (sk + sk2)

    def test_sign_verify(self):
        sk = rand_secret()
        pk = G * sk
        msg = b"What do cryptographers do when they sleep?"
        sig = sign(sk, msg)
        assert verify(sig, pk, msg)

    def sign_with_nonce(self, k: int, sk: int, msg: bytes) -> Signature:
        """Same signing method, but takes a nonce as a parameter."""
        r = G * k
        e_bytes = sha256(r.to_bytes() + msg).digest()
        e = int.from_bytes(e_bytes, "big")
        s = (k - sk * e) % generator.n
        return Signature(r, s)

    def test_nonce_reuse(self):
        sk = rand_secret()
        pk = G * sk
        k = rand_secret()
        msg1 = b"Hello"
        sig1 = self.sign_with_nonce(k, sk, msg1)
        assert verify(sig1, pk, msg1)
        msg2 = b"Goodbye"
        sig2 = self.sign_with_nonce(k, sk, msg2)
        assert verify(sig2, pk, msg2)
        solved_sk = sk_from_nonce_reuse(msg1, sig1, msg2, sig2)
        assert solved_sk == sk

    def test_threshold_signing(self):
        # 2/2 threshold signing
        # Kinda pointless to do threshold here but whatever
        sk1 = rand_secret()
        sk2 = rand_secret()
        pk1 = G * sk1
        pk2 = G * sk2
        m1 = rand_secret()
        m2 = rand_secret()
        line1 = lambda x: (m1 * x + sk1) % generator.n
        line2 = lambda x: (m2 * x + sk2) % generator.n
        idx1 = 1
        idx2 = 2
        y11 = line1(idx1)
        y12 = line1(idx2)
        y21 = line2(idx1)
        y22 = line2(idx2)
        share1 = y11 + y21
        share2 = y12 + y22
        # (x - x_m) / (x_j - x_m) * y_j
        lambda1 = (0 - idx2) * inv(idx1 - idx2, generator.n) * share1 % generator.n
        lambda2 = (0 - idx1) * inv(idx2 - idx1, generator.n) * share2 % generator.n
        sk_agg = (lambda1 + lambda2) % generator.n
        assert sk_agg == (sk1 + sk2) % generator.n
        assert lambda1 != sk1 and lambda1 != sk2
        assert lambda2 != sk1 and lambda2 != sk2
        pk_agg = G * lambda1 + G * lambda2
        assert pk_agg == pk1 + pk2

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
        sig1 = sign_with_nonce_and_agg_nonce(k1, r_agg, sk1, msg)
        sig2 = sign_with_nonce_and_agg_nonce(k2, r_agg, sk2, msg)
        sig_agg = Signature(r_agg, sig1.s + sig2.s)
        assert verify(sig_agg, pk_agg, msg)

        # Signing with the threshold key shares
        k1 = rand_secret()
        k2 = rand_secret()
        r1 = G * k1
        r2 = G * k2
        r_agg = r1 + r2
        sig1 = sign_with_nonce_and_agg_nonce(k1, r_agg, lambda1, msg)
        sig2 = sign_with_nonce_and_agg_nonce(k2, r_agg, lambda2, msg)
        sig_agg = Signature(r_agg, sig1.s + sig2.s)
        assert verify(sig_agg, pk_agg, msg)

    def test_threshold_signing2(self):
        # 2/3 threshold signing
        sk1 = rand_secret()
        sk2 = rand_secret()
        sk3 = rand_secret()
        pk1 = G * sk1
        pk2 = G * sk2
        pk3 = G * sk3
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
        # Rederiving the shared secret
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

        # Proof you can do it with only 2 of the 3 shares!
        lambda12 = (0 - idx2) * inv(idx1 - idx2, generator.n) * share1 % generator.n
        lambda21 = (0 - idx1) * inv(idx2 - idx1, generator.n) * share2 % generator.n
        sk_agg = (lambda12 + lambda21) % generator.n
        assert sk_agg == (sk1 + sk2 + sk3) % generator.n

        # Signing
        msg = b"Hello"
        k1 = rand_secret()
        k2 = rand_secret()
        r1 = G * k1
        r2 = G * k2
        r_agg = r1 + r2
        sig1 = sign_with_nonce_and_agg_nonce(k1, r_agg, lambda12, msg)
        sig2 = sign_with_nonce_and_agg_nonce(k2, r_agg, lambda21, msg)
        sig_agg = Signature(r_agg, sig1.s + sig2.s)
        pk_agg = G * lambda1 + G * lambda2 + G * lambda3
        assert pk_agg == pk1 + pk2 + pk3
        assert verify(sig_agg, pk_agg, msg)


if __name__ == "__main__":
    unittest.main()
