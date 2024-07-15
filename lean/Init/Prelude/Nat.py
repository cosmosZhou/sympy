import sympy
from std import __set__
from ..Inductive import *
from ..Type import *


class Nat(Inductive):

    def __new__(cls, n=0):
        assert isinstance(n, int)
        if not n:
            return Nat.zero
        assert n > 0
        return Nat.succ(n - 1)

    zero = Self
    succ: Self = Self

    def __str__(self):
        return str(int(self))

    @property
    def isValidChar(self) -> bool:
        return self < 0xd800 or 0xdfff < self < 0x110000

    def __bool__(self):
        return self is not self.zero


@__set__(Nat.succ)
def __new__(cls, arg):
    self = object.__new__(cls)
    self.args = arg,
    if isinstance(arg, (int, sympy.Integer)):
        assert arg >= 0
    else:
        assert isinstance(arg, Nat)
    return self


@__set__(Nat.zero.__class__)
def __int__(self):
    return 0


@__set__(Nat.succ)
def __int__(self):
    n = self.arg
    if not isinstance(n, int):
        n = int(n)
    return n + 1


@__set__(Nat.zero.__class__)
def __add__(self, rhs):
    return rhs


@__set__(Nat.zero.__class__)
def __sub__(self, rhs):
    return -rhs


@__set__(Nat.zero.__class__)
def __lt__(self, rhs):
    if isinstance(rhs, Nat.succ):
        return True
    if isinstance(rhs, int):
        return 0 < rhs
    return False


@__set__(Nat.zero.__class__)
def __le__(self, rhs):
    if isinstance(rhs, Nat.succ):
        return True
    if isinstance(rhs, int):
        return 0 <= rhs
    return True


@__set__(Nat.zero.__class__)
def __gt__(self, rhs):
    if isinstance(rhs, Nat.succ):
        return False
    if isinstance(rhs, int):
        return 0 > rhs
    return False


@__set__(Nat.zero.__class__)
def __ge__(self, rhs):
    if isinstance(rhs, Nat.succ):
        return False
    if isinstance(rhs, int):
        return 0 >= rhs
    return True


@__set__(Nat.succ)
def __lt__(self, rhs):
    if isinstance(rhs, Nat.succ):
        return self.arg < rhs.arg
    if isinstance(rhs, int):
        return int(self) < rhs
    return False


@__set__(Nat.succ)
def __le__(self, rhs):
    if isinstance(rhs, Nat.succ):
        return self.arg <= rhs.arg
    if isinstance(rhs, int):
        return int(self) <= rhs
    return False


@__set__(Nat.succ)
def __gt__(self, rhs):
    # if the __lt__ method is not defined for a class, Python will try to use the __gt__ method instead.
    if isinstance(rhs, Nat.succ):
        return self.arg > rhs.arg
    if isinstance(rhs, int):
        return int(self) > rhs
    return False


@__set__(Nat.succ)
def __ge__(self, rhs):
    # if the __lt__ method is not defined for a class, Python will try to use the __gt__ method instead.
    if isinstance(rhs, Nat.succ):
        return self.arg >= rhs.arg
    if isinstance(rhs, int):
        return int(self) >= rhs
    return False


@__set__(Nat.zero.__class__)
@property
def sign(self):
    return 0


@__set__(Nat.succ)
@property
def sign(self):
    return 1


@__set__(Nat.succ)
def __hash__(self):
    # override the default behavior of __hash__ method of Inductive type
    return hash((self.__class__, int(self)))


__all__ = 'Nat',