from std import __set__
from collections import OrderedDict
from ..Type import *
from .Compiler import *
from .Template import *



class Function(type):

    @classmethod
    def __prepare__(cls, name, bases, **__dict__):
        return TypedOrderedDict()

    def __new__(cls, name, bases, __dict__):
        cls = super().__new__(cls, name, bases, __dict__)
        if bases:
            func = cls.__new__
            func.__slots__ = func.__code__.co_varnames[1:func.__code__.co_argcount]
            func.__annotations__ = OrderedDict(
                (key, func.__annotations__[key])
                for key in (*func.__slots__, 'return')
            )

            func.__name__ = cls.__name__
            cls = Template(func, tuple(value for key, value in cls.__dict__.items() if not key.startswith('__')))
        return cls

    def __call__(cls, func):
        __slots__ = func.__code__.co_varnames[:func.__code__.co_argcount]
        __annotations__ = getattr(func, '__annotations__', {})
        Compiler.assertion(func)
        return Compiler.create_function(func, __slots__, __annotations__)


class Function(metaclass=Function):
    ...
    # def __init_subclass__(cls, /, *args, **kwargs):
        # super().__init_subclass__(*args, **kwargs)


__all__ = 'Function',