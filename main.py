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


@dataclass(frozen=True)
class Field:
    """This is a number on a prime field."""

    p: int

    def add(self, a: int, b: int) -> int:
        return (a + b) % self.p

    def sub(self, a: int, b: int) -> int:
        return (a - b) % self.p

    def mul(self, a: int, b: int) -> int:
        return (a * b) % self.p

    def inv(self, a: int) -> int:
        """Find the inverse using extended euclidean algorithm."""
        _divisor, x, _y = gcd(a, self.p)
        return x % self.p

    def div(self, a: int, b: int) -> int:
        return self.mul(a, self.inv(b))


secp256k1_field = Field(
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
)


@dataclass(frozen=True)
class Number:
    """This is a number on a prime field."""

    num: int
    field: Field = secp256k1_field

    def __add__(self, other: "Number") -> "Number":
        assert self.field == other.field
        return Number(self.field.add(self.num, other.num), self.field)

    def __sub__(self, other: "Number") -> "Number":
        assert self.field == other.field
        return Number(self.field.sub(self.num, other.num), self.field)

    def __mul__(self, other: "Number") -> "Number":
        assert self.field == other.field
        return Number(self.field.mul(self.num, other.num), self.field)

    def inv(self) -> "Number":
        return Number(self.field.inv(self.num), self.field)

    def __floordiv__(self, other: "Number") -> "Number":
        assert self.field == other.field
        return Number(self.field.div(self.num, other.num), self.field)

    def __pow__(self, other: "Number") -> "Number":
        return Number(pow(self.num, other.num, self.field.p), self.field)

    def __neg__(self) -> "Number":
        return Number(0) - self

def rand_secret() -> "Number":
    return Number(random.randrange(1, generator.n.num))


@dataclass(frozen=True)
class Curve:
    a: Number
    b: Number
    field: Field

    def eval(self, x: Number) -> Number:
        return x ** Number(3) + self.a * x + self.b

    def check(self, x: Number, y: Number) -> bool:
        """Check if the point is on the curve."""
        return y ** Number(2) == self.eval(x)


secp256k1 = Curve(
    a=Number(
        0x0000000000000000000000000000000000000000000000000000000000000000
    ),  # a = 0
    b=Number(
        0x0000000000000000000000000000000000000000000000000000000000000007
    ),  # b = 7
    field=secp256k1_field,
)


@dataclass(frozen=True)
class Point:
    curve: Curve
    x: Number
    y: Number

    @staticmethod
    def inf() -> "Point":
        return Point(secp256k1, Number(None), Number(None))

    def __add__(self, other: "Point") -> "Point":
        # P + 0 = 0 + P
        if self == Point.inf():
            return other
        if other == Point.inf():
            return self
        # P + (-P) = 0
        if self.x == other.x and self.y != other.y:
            return Point.inf()
        # slope
        if self.x == other.x:
            m = (Number(3) * (self.x ** Number(2)) + self.curve.a) // (Number(2) * self.y)
        else:
            m = (self.y - other.y) // (self.x - other.x)
        x = m ** Number(2) - self.x - other.x
        y = -(m * (x - self.x) + self.y)
        return Point(self.curve, x, y)

    def __mul__(self, k_num: Number) -> "Point":
        k = k_num.num
        assert isinstance(k, int) and k >= 0
        result = Point.inf()
        append = self
        while k > 0:
            if k & 1:
                result += append
            append += append
            k >>=1
        return result

    def to_bytes(self) -> bytes:
        return bytes([2 if self.y.num % 2 == 0 else 3]) + int.to_bytes(self.x.num, 32, "big") # big endian


G = Point(
    secp256k1,
    x=Number(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798),
    y=Number(0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8),
)


@dataclass(frozen=True)
class Generator:
    G: Point
    n: Number


generator = Generator(
    G=G,
    # the order of G is known and can be mathematically derived
    n=Number(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141),
)

@dataclass
class Signature:
    s: Number
    e: Number

def sign(sk: Number, msg: bytes) -> Signature:
    """Returns (s, e) where
        r = k * G
        e = H(r || msg)
        s = k + sk * e
    """
    k = rand_secret()
    r = G * k
    print("r:", r.to_bytes())
    print("r.x:", r.x.num)
    e_bytes = sha256(r.to_bytes() + msg).digest()
    print("e_bytes:", e_bytes)
    e = Number(int.from_bytes(e_bytes, "big"))
    s = k + sk * e
    return Signature(s, e), k

def verify(sig: Signature, pk: Point, msg: bytes) -> bool:
    # G * s = G * (k + sk * e)
    # pk * e = G * (-sk * e)
    # r = G * k
    r = G * sig.s + pk * sig.e
    print("verify r:", r.to_bytes())
    print("verify r.x:", r.x.num)
    e_bytes = sha256(r.to_bytes() + msg).digest()
    print("verify e_bytes:", e_bytes)
    e = Number(int.from_bytes(e_bytes, "big"))
    print("verify e:", e)
    return sig.e == e

class TestThresholdSigning(unittest.TestCase):
    def test_curve(self):
        assert secp256k1.check(G.x, G.y)

        x = Number(random.randrange(0, secp256k1_field.p))
        y = Number(random.randrange(0, secp256k1_field.p))
        assert not secp256k1.check(x, y)

        pk = G + G
        assert secp256k1.check(pk.x, pk.y)

        pk = G + G + G
        assert secp256k1.check(pk.x, pk.y)

        assert G * Number(2) == G + G
        assert G * Number(3) == G + G + G

        assert -Number(2) == Number(0) - Number(2)
        print((-Number(2)).num)
        print((Number(2)).num)
        print((Number(2).field.p))

        assert G * Number(2) * Number(3) == G * Number(6)
        sk = rand_secret()
        sk2 = rand_secret()
        assert sk + sk2 == sk2 + sk
        print("sk:", sk.num)
        print("sk2:", sk2.num)
        print("sk + sk2:", (sk + sk2).num)
        print("sk2 + sk:", (sk2 + sk).num)
        print("G * sk:", (G * sk).x.num)
        print("G * sk2:", (G * sk2).x.num)
        print("G * sk + G * sk2:", (G * sk + G * sk2).x.num)
        print("G * (sk + sk2):", (G * (sk + sk2)).x.num)
        assert G * sk + G * sk2 == G * (sk + sk2)


    # def test_sign_verify(self):
    #     sk = rand_secret()
    #     pk = G * sk
    #     verify_pk = G * -sk
    #     msg = b"What do cryptographers do when they sleep?"
    #     sig, k = sign(sk, msg)
    #     print("s:", sig.s.num)
    #     print("e:", sig.e.num)
    #     assert sig.s - k == sk * sig.e
    #     assert sig.s + (-sk * sig.e) == k
    #     assert G * (sig.s - k) == G * (sk * sig.e)
    #     assert verify_pk * sig.e == G * (-sk * sig.e)
    #     assert G * (sig.s + (-sk * sig.e)) == G * k
    #     assert G * sig.s + G * (-sk * sig.e) == G * k
    #     assert verify(sig, verify_pk, msg)


if __name__ == "__main__":
    unittest.main()
