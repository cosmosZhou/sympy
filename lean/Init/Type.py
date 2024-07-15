from collections import OrderedDict
from typing import Self
from sympy import Symbol


class Type:
    
    def __new__(cls, arg):
        if isinstance(arg, str):
            self = super().__new__(cls)
            self.name = arg
            return self
        else:
            assert isinstance(arg, type)
            dtype = arg
            return Symbol('', domain=dtype)

    def __repr__(self):
        return self.name
    
    def __eq__(self, other):
        return isinstance(other, Type) and self.name == other.name
        
    def __hash__(self):
        return hash(self.name)
        
    __str__ = __repr__

    def __matmul__(cls, rhs):
        # return cls @ rhs
        from .Prelude.Prod import Prod
        if cls.__mro__[1] is Prod.cls:
            return cls.__annotations__['fst'] @ (cls.__annotations__['snd'] @ rhs)
        return Prod[cls, rhs]

    def __rmatmul__(cls, lhs):
        # return lhs @ cls
        from .Prelude.Prod import Prod
        if lhs.__mro__[1] is Prod.cls:
            return lhs.__annotations__['fst'] @ (lhs.__annotations__['snd'] @ cls)
        return Prod[lhs, cls]

    def __or__(cls, rhs):
        # return cls | rhs
        from .Core.Sum import Sum
        return Sum[cls, rhs]

    def __ror__(cls, lhs):
        # return lhs | cls
        from .Core.Sum import Sum
        return Sum[lhs, cls]


class TypedOrderedDict(OrderedDict):

    def __setitem__(self, key, value):
        if value is Type:
            value = Type(key)
        elif isinstance(value, Symbol) and not value.name:
            value.name = key
        super().__setitem__(key, value)


__all__ = 'Type', 'TypedOrderedDict', 'Self', 'OrderedDict'