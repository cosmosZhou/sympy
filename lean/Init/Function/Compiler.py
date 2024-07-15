import ast, inspect, sympy, re, types
from sympy import Symbol
from std import computed
from .sympy_expr import *
from ..Type import *
from .Template import *


# https://en.wikipedia.org/wiki/Halting_problem
class Compiler(ast.NodeVisitor):
    
    def __init__(self, func, cls=None):
        self.func = func
        # Get the source code of the function
        self.source = inspect.getsource(func)
        self.cls = cls

    @computed
    def indent(self):
        return len(re.match('\s*', self.source)[0]) // 4

    def unindent(self):
        self.source = '\n'.join(line[self.indent * 4:] for line in self.source.split('\n'))

    def visit_Call(self, node):
        # Check if the function call is to the function we are analyzing
        if isinstance(node.func, ast.Name) and node.func.id == self.func.__name__:
            self.is_recursive = True
        self.generic_visit(node)

    def visit_Subscript(self, node):
        # Check if it is a template function call:
        if isinstance(node.value, ast.Name) and node.value.id == self.func.__name__ and self.func.__qualname__.endswith('.__new__'):
            self.is_recursive = True
        self.generic_visit(node)

    @computed
    def parsingTree(self):
        # Parse the source code into an AST
        return ast.parse(self.source)

    @computed
    def is_recursive(self):
        repetition = len(re.findall('\\b' + self.func.__name__ + '\\b', self.source))
        if self.source.startswith('    def __new__('):
            hit = repetition > 0
            self.source = '\n'.join(line[4:] for line in self.source.split('\n'))
        else:
            hit = repetition > 1
        if hit:
            self.is_recursive = None
            # Visit the AST nodes
            self.visit(self.parsingTree)
            return self.is_recursive
    
    @is_recursive.setter
    def is_recursive(self, is_recursive):
        self.__dict__['is_recursive'] = is_recursive

    @property
    def is_infinitely_recursive(self):
        if self.is_recursive:
            expr = self.sympy_expr(self.locals)
            func = self.sympy_func
            vars = tuple(self.sympy_args.values())
            func.eval = sympy.Lambda(vars, expr)
            return func.is_infinitely_recursive

    @computed
    def sympy_func(self):
        kwargs = {}
        func = self.func
        dtype = func.__annotations__['return']
        match dtype.__name__:
            case 'bool':
                kwargs['bool'] = True
            case 'int':
                kwargs['integer'] = True
            case 'float':
                kwargs['real'] = True
            case 'complex':
                kwargs['complex'] = True
            case _:
                kwargs['domain'] = dtype
        return sympy.Function(func.__name__, **kwargs)

    @computed
    def locals(self):
        func = self.func
        if isinstance(func, type):
            return OrderedDict()

        globals = func.__globals__
        locals = OrderedDict(
            (var, globals[var])
            for var in func.__code__.co_names if var in globals
        )
        if self.is_recursive:
            sympy_func = self.sympy_func
            if isinstance(locals[func.__name__], Template):
                dtypes = self.cls.__dtypes__
                if len(dtypes) == 1:
                    dtypes, = dtypes
                sympy_func = {dtypes: sympy_func}
            locals[func.__name__] = sympy_func
        return locals | self.sympy_args

    @computed
    def sympy_args(self):
        # Extract argument information
        func = self.func
        kwargs = OrderedDict()
        __annotations__ = func.__annotations__
        for var in inspect.signature(func).parameters:
            if dtype := __annotations__.get(var):
                if dtype is Type:
                    val = var
                elif isinstance(dtype, type):
                    val = Symbol(var, domain=dtype)
                elif isinstance(dtype, dict):
                    [cls, args],  = dtype.items()

                    assert isinstance(args, tuple), f'Expected tuple, got {type(args)}'
                    args = [*args]
                    for name, dtype in zip(self.cls.__args__, self.cls.__dtypes__):
                        for i, arg in enumerate(args):
                            if name == arg:
                                args[i] = dtype

                    val = Symbol(var, domain=cls[tuple(args)])
                elif dtype.is_integer:
                    if dtype.is_nonnegative:
                        val = Symbol(var, integer=True, negative=False)
                    else:
                        val = Symbol(var, integer=True)
                elif dtype.is_rational:
                    val = Symbol(var, rational=True)
                elif dtype.is_real:
                    val = Symbol(var, real=True)
                elif dtype.is_complex:
                    val = Symbol(var, complex=True)
                else:
                    raise TypeError(f'Unsupported type {dtype}')
            else:
                assert var == 'cls', f'Expected cls, got {var}'
                val = self.cls

            kwargs[var] = val
            # print(val.domain, val.dtype)
        
        return kwargs

    def sympy_expr(self, locals):
        return self.parsingTree.body[0].sympy_expr(locals)

    @classmethod
    def assertion(cls, func, __cls__=None):
        assert not Compiler(func, cls=__cls__).is_infinitely_recursive, f'''
fail to show termination for
{func.__name__}
with errors
structural recursion cannot be used

well-founded recursion cannot be used, '{func.__name__}' does not take any (non-fixed) arguments
'''

    @classmethod
    def create_function(cls, func, __slots__, __annotations__):
        __spec__ = [(var, __annotations__[var], None) for var in __slots__]
        if __kwdefaults__ := func.__kwdefaults__:
            for key, value in __kwdefaults__.items():
                index = __slots__.index(key)
                __spec__[index] = __spec__[index][:-1], value

        __spec__ = tuple(__spec__)

        return_type = __annotations__['return']
        if isinstance(return_type, types.FunctionType):
            co_varnames = return_type.__code__.co_varnames
            indices = []
            for i, (key, dtype, default) in enumerate(__spec__):
                if key in co_varnames:
                    indices.append(i)
            
            indices = tuple(indices)

        def function(*args, **kwargs):
            args = [*args]
            for i, (key, dtype, default) in enumerate(__spec__):
                if i >= len(args):
                    args.append(kwargs.get(key, default))
                if not isinstance(args[i], dtype):
                    args[i] = dtype(args[i])
            ret = func(*args)

            if isinstance(dtype := return_type, types.FunctionType):
                dtype = dtype(*(args[index] for index in indices))

            if not isinstance(ret, dtype):
                ret = dtype(ret)
            return ret
        return function


__all__ = 'Compiler',