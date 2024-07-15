from ..Structure import *
from ..Type import *


class Prod(Structure):
    α = Type
    β = Type
    # Constructs a pair from two terms.

    # The first projection out of a pair. if `p : α × β` then `p.1 : α`.
    fst = α
    # The second projection out of a pair. if `p : α × β` then `p.2 : β`.
    snd = β

    def __str__(self):
        return "(%s)" % ", ".join(str(arg) for arg in iter(self))

    def __iter__(self):
        if self.__class__.__annotations__['snd'].__mro__[1] is Prod.cls:
            yield self.args[0]
            yield from self.args[1]
        else:
            yield from self.args
    
    def __new__(cls, *args):
        if len(args) == 2:
            self = super().__new__(cls)
            args = [*args]
            for i, (key, dtype, default) in enumerate(cls.__spec__):
                assert i < len(args)
                if not isinstance(args[i], dtype):
                    args[i] = dtype(args[i])
            self.args = tuple(args)
            return self
        else:
            assert len(args) > 2
            return cls(args[0], cls.__annotations__['snd'](*args[1:]))


__all__ = 'Prod',