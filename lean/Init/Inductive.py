import std
from std import __set__
from .Function import Compiler
from .Type import *
from sympy.core.symbol import dtype


# inductive Datatype in lean4 style:
class Inductive(type):

    def create_subclass(cls, __name__, dtype):
        if not isinstance(dtype, tuple):
            dtype = dtype,
        
        dtype = tuple(cls if type is Self else type for type in dtype)

        class Inductive(cls):

            def __new__(cls, *args):
                self = object.__new__(cls)
                argsModified = {}
                for i, (arg, type) in enumerate(zip(args, dtype)):
                    if not isinstance(arg, type):
                        argsModified[i] = type(arg)
                if argsModified:
                    args = list(args)
                    for i, arg in argsModified.items():
                        args[i] = arg
                    args = tuple(args)
                self.args = args
                return self

            def __repr__(self):
                args = self.args
                args = ", ".join(repr(arg) for arg in args)
                return f'{self.__class__.__name__}({args})'
            
            __str__ = cls.__str__

        @__set__(Inductive)
        @property
        def arg(self):
            return self.args[0]

        Inductive.__name__ = f"{cls.__name__}.{__name__}"
        return Inductive

    @classmethod
    def __prepare__(cls, name, bases, **__dict__):
        return TypedOrderedDict()

    def __new__(cls, name, bases, __dict__):
        cls = super().__new__(cls, name, bases, __dict__)
        # assert isinstance(cls, type)
        if bases and (__slots__ := tuple(key for key, value in __dict__.items() if not key.startswith('__') and not isinstance(value, property))):
            # from typing import get_type_hints
            __annotations__ = __dict__.get('__annotations__', {})
            if any(isinstance(__dict__[key], Type) for key in __slots__):
                # lean4 version of inductive type with different constructors:
                parser = Compiler(cls)
                if parser.indent:
                    # we don't parse inner structures within a function or class
                    return cls
                __args__, __spec__ = std.array_split(
                    ((key, __dict__[key]) for key in __slots__), 
                    cls.split_args
                )
                for var, dtype in __spec__:
                    if var in __annotations__:
                        dtype = __annotations__.pop(var), dtype
                    __annotations__[var] = dtype

                cls.__annotations__ = __annotations__
                cls.__slots__ = tuple(slot for slot in __slots__ if slot in __annotations__)
                cls = Template(cls, tuple(OrderedDict(__args__).values()))
            else:
                cls.__slots__ = __slots__
                cls.create_class(__slots__, __annotations__, __dict__)
        return cls

    def create_class(cls, __slots__, __annotations__, __dict__):
        for key in __slots__:
            assert __dict__[key] is Self, f'{key} is not Self'
            if key in __annotations__:
                setattr(cls, key, cls.create_subclass(key, __annotations__[key]))
            else:
                # constant values of the inductive type
                class Constant(cls):

                    def __new__(cls, *args):
                        self = object.__new__(cls)
                        self.args = args
                        return self

                    def __repr__(self):
                        return self.__class__.__name__
                    
                    if cls.__mro__[0].__str__ is cls.__mro__[1].__str__:
                        # if the class has no __str__ method, __str__ is defaulted to __repr__ method
                        __str__ = __repr__

                Constant.__name__ = f'{cls.__name__}.{key}'

                @__set__(Constant)
                @property
                def is_number(self):
                    ...

                setattr(cls, key, Constant())

    def split_args(cls, item):
        var, expr = item
        return isinstance(expr, Type) and var == expr.name

    __matmul__ = Type.__matmul__
    __rmatmul__ = Type.__rmatmul__

    __or__ = Type.__or__
    __ror__ = Type.__ror__

    @property
    def etype(cls):
        if not cls.__subclasses__():
            cls = cls.__mro__[1]
        return dtype.type(cls)

    @property
    def free_symbols(cls):
        return set()


class Inductive(metaclass=Inductive):

    # def __init_subclass__(cls, /, *args, **kwargs):
        # super().__init_subclass__(*args, **kwargs)

    def __eq__(self, other):
        return isinstance(other, self.__class__) and self.args == other.args

    def __hash__(self):
        return hash((self.__class__, *self.args))

    @property
    def dtype(self):
        return dtype.type(self.__class__.__mro__[1])


# inductive Datatype in lean4 style:
class Template:

    def __init__(self, cls, __args__):
        self.cache = {}
        self.cls = cls  # template class
        self.__args__ = __args__  # template arguments

    def __getitem__(self, dtypes):
        if not isinstance(dtypes, tuple):
            dtypes = dtypes,

        __args__ = self.__args__
        if len(dtypes) < len(__args__):
            dtypes += __args__[len(dtypes):]

        if any(isinstance(dtype, Type) for dtype in dtypes):
            return {self: dtypes}

        if new_class := std.getitem(self.cache, *dtypes):
            return new_class
        
        cls = self.cls
        __dict__ = cls.__dict__
        __annotations__ = {}
        for name, dtype in zip(__args__, dtypes):
            assert isinstance(dtype, type), f'{dtype} is not a type'
            for key, value in cls.__annotations__.items():
                if isinstance(value, tuple):
                    input_dtype, return_dtype = value
                    assert return_dtype == __dict__[key]
                    if isinstance(input_dtype, Type):
                        if name == input_dtype:
                            __annotations__[key] = dtype
                    elif isinstance(input_dtype, tuple):
                        # possible bugs here:
                        __annotations__[key] = tuple(
                            dtype if name == arg else arg 
                            for arg in input_dtype
                        )

        class Inductive(cls):
            ...
        
        Inductive.__name__ = "%s[%s]" % (cls.__name__,  ', '.join(dtype.__name__ for dtype in dtypes))
        Inductive.__annotations__ = __annotations__
        Inductive.create_class(cls.__slots__, __annotations__, __dict__)
        std.setitem(self.cache, *dtypes, Inductive)
        return Inductive


__all__ = 'Inductive',