from .Nat import *
from ..Structure import *
from ..Type import *


# `Fin n` is a natural number `i` with the constraint that `0 ≤ i < n`.
# It is the "canonical type with `n` elements".
class Fin(Structure):
    
    n = Type(Nat)
    # Creates a `Fin n` from `i : Nat` and a proof that `i < n`.
    # If `i : Fin n`, then `i.val : ℕ` is the described number. It can also be written as `i.1` or just `i` when the target type is known.
    val = Nat
    # If `i : Fin n`, then `i.2` is a proof that `i.1 < n`.
    @property
    def isLt(self):
        return self.val < self.n

    def __int__(self):
        return int(self.val)


__all__ = 'Fin',