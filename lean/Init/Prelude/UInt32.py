from ..Structure import *
from .Nat import *
from .Fin import *


# The type of unsigned 32-bit integers. This type has special support in the
# compiler to make it actually 32 bits rather than wrapping a `Nat`.
class UInt32(Structure):
    # Unpack a `UInt32` as a `Nat` less than `2 ** 32`.
    # This function is overridden with a native implementation.
    val = Fin[2 ** 32]

    @property
    def isValidChar(self) -> bool:
        return self.toNat.isValidChar

    @property
    def toNat(self) -> Nat:
        return self.val.val

    def __int__(self):
        return int(self.val)


__all__ = 'UInt32',