from ..Type import *
from ..Inductive import *


class Sum(Inductive):
    α = Type
    β = Type
    # Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`.
    inl: α = Self
    # Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`.
    inr: β = Self
