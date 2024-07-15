import std
from ..Type import *


# C++ template function
class Template:
    '''
    lean4 version of the C++ template function:
    template <typename α, typename β, typename γ>
    auto function(α x, β y) -> γ {
        return static_cast<γ>(std::pow(x, y));
    }
    '''
    def __init__(self, func, __args__):
        self.cache = {}
        self.func = func  # template function
        self.__args__ = __args__  # template arguments
        assert __args__, f'{func.name} has no template arguments'
    
    def __getitem__(self, dtypes):
        if not isinstance(dtypes, tuple):
            dtypes = dtypes,
        
        __args__ = self.__args__
        if len(dtypes) < len(__args__):
            dtypes += __args__[len(dtypes):]

        if function := std.getitem(self.cache, *dtypes):
            return function

        func = self.func
        __annotations__ = OrderedDict(func.__annotations__)
        for key, value in __annotations__.items():
            if isinstance(value, dict):
                (cls, args), = value.items()
                assert isinstance(args, tuple), f'Expected tuple, got {type(args)}'
                args = [*args]
                for name, dtype in zip(__args__, dtypes):
                    for i, arg in enumerate(args):
                        if name == arg:
                            args[i] = dtype

                __annotations__[key] = cls[tuple(args)]
            elif isinstance(value, Type):
                for name, dtype in zip(__args__, dtypes):
                    if name == value:
                        __annotations__[key] = dtype
                        break

        from .Compiler import Compiler
        cls = std.Object()
        for var, dtype in zip(__args__, dtypes):
            assert isinstance(dtype, type), f'Expected type, got {dtype}'
            cls[var.name] = dtype
        cls.__args__ = __args__
        cls.__dtypes__ = dtypes
        Compiler.assertion(func, cls)
        function = Compiler.create_function(lambda *args: func(cls, *args), func.__slots__, __annotations__)
        std.setitem(self.cache, *dtypes, function)
        return function

    def __call__(self, *args):
        func = self.func
        assert len(args) + 1 == len(func.__annotations__)  # self.__annotations__ has an extra 'return' key!
        # determine the template args automatically
        __args__ = self.__args__
        _Ty = [None] * len(__args__)
        for arg, annotation in zip(args, func.__annotations__.values()):
            if isinstance(annotation, dict):
                (cls, annotated_args), = annotation.items()
                __mro__ = arg.__class__.__mro__
                if realized_annotations := __mro__[0].__annotations__:
                    # template structure types
                    for key, template_arg in __mro__[1].__annotations__.items():
                        if realized_arg := realized_annotations.get(key):
                            if isinstance(template_arg, Type):
                                try:
                                    index = __args__.index(template_arg)
                                    assert template_arg in annotated_args, f'Expected {template_arg} in {annotated_args}'
                                    if _Ty[index]:
                                        assert _Ty[index] == realized_arg, f'Expected {_Ty[index]} == {realized_arg}'
                                    else:
                                        _Ty[index] = realized_arg
                                except ValueError:
                                    ...
                else:
                    realized_annotations = __mro__[1].__annotations__
                    # template inductive types
                    for key, template_annotation in __mro__[2].__annotations__.items():
                        if realized_annotation := realized_annotations.get(key):
                            if isinstance(template_annotation, tuple):
                                template_args_annotation, template_return_annotation = template_annotation
                                if isinstance(template_args_annotation, tuple):
                                    assert isinstance(realized_annotation, tuple)
                                    for template_arg, realized_arg in zip(template_args_annotation, realized_annotation):
                                        try:
                                            index = __args__.index(template_arg)
                                            assert template_arg in annotated_args, f'Expected {template_arg} in {annotated_args}'
                                            if _Ty[index]:
                                                assert _Ty[index] == realized_arg, f'Expected {_Ty[index]} == {realized_arg}'
                                            else:
                                                _Ty[index] = realized_arg
                                        except ValueError:
                                            ...
        try:
            index = _Ty.index(None)
            raise Exception(f"could not deduce template argument for '{__args__[index]}'")
        except ValueError:
            return self[tuple(_Ty)](*args)


__all__ = 'Template',