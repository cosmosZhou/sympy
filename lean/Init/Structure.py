import std
from collections import OrderedDict
from std import __set__
from .Function import Compiler
from .Type import *
from sympy import Symbol


# structure Datatype in lean4 style:
class Structure(type):

    @classmethod
    def __prepare__(cls, name, bases, **__dict__):
        return TypedOrderedDict()

    def __new__(cls, name, bases, __dict__):
        cls = super().__new__(cls, name, bases, __dict__)
        # assert isinstance(cls, type)
        if bases:
            __slots__ = __dict__.get('__slots__') or tuple(key for key, value in __dict__.items() if not key.startswith('__') and not isinstance(value, property))
            assert __slots__, f'{name} has no slots'
            __annotations__ = __dict__.get('__annotations__', {})
            __spec__ = []
            for key in __slots__:
                if key in __annotations__:
                    dtype = __annotations__[key]
                    default = __dict__.get(key)
                else:
                    dtype = __dict__[key]
                    default = None
                __spec__.append((key, dtype, default))

            if any(isinstance(dtype, (Type, Symbol)) for key, dtype, default in __spec__):
                parser = Compiler(cls)
                if parser.indent:
                    # we don't parse inner structures within a function or class
                    return cls

                __args__, __annotations__ = std.array_split(
                    ((key, __dict__[key]) for key in __slots__), 
                    cls.split_args
                )                

                cls.__annotations__ = OrderedDict(__annotations__)
                return Template(cls, tuple(OrderedDict(__args__).values()))

            __spec__ = tuple(__spec__)
            cls.__spec__ = __spec__
            cls.__slots__ = __slots__

            # constant values of the structure type
            if cls.__mro__[1].__new__ is cls.__mro__[2].__new__ and cls.__mro__[0].__new__ is cls.__mro__[1].__new__:
                # if the class has no __new__ method, we can use the default __init__ method
                @__set__(cls)
                def __init__(self, *args, **kwargs):
                    args = [*args]
                    for i, (key, dtype, default) in enumerate(__spec__):
                        if i >= len(args):
                            args.append(kwargs.get(key, default))
                        if not isinstance(args[i], dtype):
                            args[i] = dtype(args[i])
                    self.args = tuple(args)

            @__set__(cls)
            def __repr__(self):
                args = self.args
                args = ", ".join(f"{key} := {arg}" for key, arg in zip(__slots__, args))
                return f'{{{args} : {cls.__name__}}}'
                
            for i, slot in enumerate(__slots__):
                setattr(cls, slot, (lambda i: property(lambda self: self.args[i]))(i))

            if cls.__mro__[1].__str__ is cls.__mro__[2].__str__ and cls.__mro__[0].__str__ is cls.__mro__[1].__str__:
                # if the class has no __str__ method, __str__ is defaulted to __repr__ method
                cls.__str__ = cls.__repr__

        return cls

    def split_args(cls, item):
        var, expr = item
        return isinstance(expr, (Type, Symbol)) and var == expr.name

    def create_structure(cls, annotations, dtypes):
        class Structure(cls):
            __slots__ = tuple(annotations)
            __annotations__ = annotations

        args = ', '.join(str(dtype) for dtype in dtypes)
        Structure.__name__ = f"{cls.__name__}[{args}]"
        return Structure

    __matmul__ = Type.__matmul__
    __rmatmul__ = Type.__rmatmul__

    __or__ = Type.__or__
    __ror__ = Type.__ror__


class Structure(metaclass=Structure):

    # def __init_subclass__(cls, /, *args, **kwargs):
        # super().__init_subclass__(*args, **kwargs)
        
    def __call__(self, **kwargs):
        cls = self.__class__
        args = self.args
        for i, (attr, dtype, defaultVal) in enumerate(cls.__spec__):
            if attr in kwargs:
                value = kwargs.pop(attr)
                assert isinstance(value, dtype), f'Expected {dtype}, got {type(value)}'
                args = args[:i] + (value,) + args[i + 1:]
        assert not kwargs, f'Unknown arguments: {kwargs}'
        return cls(*args)

    def __eq__(self, other):
        return isinstance(other, self.__class__) and self.args == other.args

    def __hash__(self):
        return hash((self.__class__, *self.args))


# lean4 version of the C++ template structure type
class Template:
    '''
    template <typename α, typename β> 
    struct structure {
        α x;
        β y;
        int z;
    };
    '''

    def __init__(self, cls, __args__):
        self.cache = {}
        self.cls = cls  # template structure
        self.__args__ = __args__  # template arguments
        
    def __getitem__(self, dtypes):
        if not isinstance(dtypes, tuple):
            dtypes = dtypes,
        
        __args__ = self.__args__
        if len(dtypes) < len(__args__):
            dtypes += tuple(dtype.dtype for dtype in __args__[len(dtypes):])

        if any(isinstance(dtype, (Type, Symbol)) for dtype in dtypes):
            return {self: dtypes}

        for i, (dtype, name) in enumerate(zip(dtypes, __args__)):
            if isinstance(name, Symbol) and not isinstance(dtype, name.domain):
                dtypes = dtypes[:i] + (name.domain(dtype),) + dtypes[i + 1:]

        if new_class := std.getitem(self.cache, *dtypes):
            return new_class

        cls = self.cls
        __annotations__ = OrderedDict(cls.__annotations__)
        for dtype, name in zip(dtypes, __args__):
            if isinstance(dtype, type):
                for key, value in __annotations__.items():
                    if name == value:
                        __annotations__[key] = dtype

        new_class = cls.create_structure(__annotations__, dtypes)

        for dtype, name in zip(dtypes, __args__):
            if isinstance(name, Symbol):
                setattr(new_class, name.name, dtype)

        std.setitem(self.cache, *dtypes, new_class)
        return new_class


__all__ = 'Structure',