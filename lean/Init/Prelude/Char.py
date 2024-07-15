from ..Inductive import *
from ..Structure import *
from .UInt32 import *


# The `Char` Type represents an unicode scalar value. See http://www.unicode.org/glossary/#unicode_scalar_value).
class Char(Structure):
    # The underlying unicode scalar value as a `UInt32`.
    val = UInt32
    # The value must be a legal codepoint.
    @property
    def valid(self):
        return self.val.isValidChar

    def __new__(cls, val):
        if isinstance(val, str):
            val = ord(val)

        if not isinstance(val, UInt32):
            val = UInt32(val)

        self = super().__new__(cls)
        self.args = val,
        assert self.valid, f'Invalid Char: {val}'
        return self

    def __str__(self):
        ch = chr(int(self.val))
        ch = ch.replace("'", "\\'")
        return f"'{ch}'"


__all__ = 'Char',