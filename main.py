from typing import Tuple
import unittest
from dataclasses import dataclass
import random

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
        return Point(secp256k1, Number(0), Number(0))

    def __add__(self, other: "Point") -> "Point":
        # P + 0 = 0 + P
        if self == Point.inf():
            return other
        if other == Point.inf():
            return self
        # P + (-P) = 0
        if self.x == other.x and self.y == -other.y:
            return Point.inf()
        # slope
        if self.x == other.x:
            m = (Number(3) * self.x ** Number(2) + self.curve.a) // (Number(2) * self.y)
        else:
            m = (other.y - self.y) // (other.x - self.x)
        x = m ** Number(2) - self.x - other.x
        y = -(m * (x - self.x) + self.y)
        return Point(self.curve, x, y)

    def __mul__(self, k: Number) -> "Point":
        assert isinstance(k, Number) and k.num >= 0
        result = Point.inf()
        append = self
        while k.num > 0:
            if k.num & 1:
                result += append
            append += append
            k = Number(k.num >> 1)
        return result


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


if __name__ == "__main__":
    unittest.main()
