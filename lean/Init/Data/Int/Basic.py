from std import __set__
from ...Inductive import *
from ...Prelude import *
from ...Type import *


class Int(Inductive):

    def __new__(cls, n=0):
        assert isinstance(n, int)
        if n >= 0:
            return Int.ofNat(Nat(n))
        return Int.negSucc(Nat(-n))

    # A natural number is an integer (`0` to `∞`).
    ofNat: Nat = Self
    # The negation of the successor of a natural number is an integer (`-1` to `-∞`).
    negSucc: Nat = Self

    def __lt__(self, rhs):
        return int(self) < int(rhs)

    def __gt__(self, rhs):
        return int(self) > int(rhs)

    def __le__(self, rhs):
        return int(self) <= int(rhs)
    
    def __ge__(self, rhs):
        return int(self) >= int(rhs)

    def __add__(self, rhs):
        return Int(int(self) + int(rhs))

    def __sub__(self, rhs):
        return Int(int(self) - int(rhs))

    def __int__(self):
        return int(self.arg) * self.sign


@__set__(Int.ofNat)
def __str__(self):
    return str(self.arg)


@__set__(Int.negSucc)
def __str__(self):
    return '-' + str(self.arg)


@__set__(Int.ofNat)
@property
def sign(self):
    return self.arg.sign


@__set__(Int.negSucc)
@property
def sign(self):
    return -1


@__set__(Nat.succ)
def __sub__(self, rhs):
    sum = Int(int(self) - int(rhs))
    if sum >= 0:
        return sum.arg
    return sum


@__set__(Nat.succ)
def __add__(self, rhs):
    sum = Int(int(self) + int(rhs))
    if sum >= 0:
        return sum.arg
    return sum


@__set__(Nat.succ)
def __sub__(self, rhs):
    sum = Int(int(self) - int(rhs))
    if sum >= 0:
        return sum.arg
    return sum


__all__ = 'Int',