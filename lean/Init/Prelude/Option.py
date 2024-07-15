from ..Inductive import *
from ..Type import *


class Option(Inductive):

    α = Type
    # No value.
    none = Self
    # Some value of type `α`.
    some: α = Self


__all__ = 'Option',