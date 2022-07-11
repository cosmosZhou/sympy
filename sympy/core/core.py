""" The core's core. """
# used for canonical ordering of symbolic sequences
# via __cmp__ method:
# FIXME this is *so* irrelevant and outdated!
from sympy.core.cache import cacheit
ordering_of_classes = [
    # singleton numbers
    'Zero', 'One', 'Half', 'Infinity', 'NaN', 'NegativeOne', 'NegativeInfinity',
    # numbers
    'Integer', 'Rational', 'Float',
    # singleton symbols
    'Exp1', 'Pi', 'ImaginaryUnit',
    # symbols
    'Symbol', 'Wild', 'Temporary',
    # arithmetic operations
    'Pow', 'Mul', 'Add',
    # function values
    'Derivative', 'Integral',
    # defined singleton functions
    'Abs', 'Sign', 'Sqrt',
    'Floor', 'Ceiling',
    'Re', 'Im', 'Arg',
    'Conjugate',
    'Exp', 'Log',
    'Sin', 'Cos', 'Tan', 'Cot', 'ASin', 'ACos', 'ATan', 'ACot',
    'Sinh', 'Cosh', 'Tanh', 'Coth', 'ASinh', 'ACosh', 'ATanh', 'ACoth',
    'RisingFactorial', 'FallingFactorial',
    'factorial', 'binomial',
    'Gamma', 'LowerGamma', 'UpperGamma', 'PolyGamma',
    'Erf',
    # special polynomials
    'Chebyshev', 'Chebyshev2',
    # undefined functions
    'Function', 'WildFunction',
    # anonymous functions
    'Lambda',
    # Landau O symbol
    'Order',
    # relational operations
    'Equal', 'Unequal', 'Greater', 'Less',
    'GreaterEqual', 'LessEqual',
]


class Registry(object):
    """
    Base class for registry objects.

    Registries map a name to an object using attribute notation. Registry
    classes behave singletonically: all their instances share the same state,
    which is stored in the class object.

    All subclasses should set `__slots__ = []`.
    """
    __slots__ = []

    def __setattr__(self, name, obj):
        setattr(self.__class__, name, obj)

    def __delattr__(self, name):
        delattr(self.__class__, name)


# A set containing all sympy class objects
all_classes = set()


class BasicMeta(type):

    def __init__(cls, *args, **kws):
        all_classes.add(cls)

    def __cmp__(self, other):
        # If the other object is not a Basic subclass, then we are not equal to
        # it.
        if not isinstance(other, BasicMeta):
            return -1
        n1 = self.__name__
        n2 = other.__name__
        if n1 == n2:
            return 0

        UNKNOWN = len(ordering_of_classes) + 1
        try:
            i1 = ordering_of_classes.index(n1)
        except ValueError:
            i1 = UNKNOWN
        try:
            i2 = ordering_of_classes.index(n2)
        except ValueError:
            i2 = UNKNOWN
        if i1 == UNKNOWN and i2 == UNKNOWN:
            return (n1 > n2) - (n1 < n2)
        return (i1 > i2) - (i1 < i2)

    # self < other
    def lt(self, other):
        if self.__cmp__(other) == -1:
            return True
        return False

    # self > other
    def gt(self, other):
        if self.__cmp__(other) == 1:
            return True
        return False

    def __or__(self, other):
        from sympy.core.of import Basic, sympify
        other = sympify(other)
        if self.is_Boolean:
            from sympy import Or
            obj = Basic.__new__(Or, self, other)
        else:
            from sympy import Union
            obj = Basic.__new__(Union, self, other)
        return obj            
    
    def __and__(self, other):
        from sympy.core.of import Basic, sympify
        other = sympify(other)
        if self.is_Boolean:
            from sympy import And
            obj = Basic.__new__(And, self, other)
        else:
            from sympy import Intersection
            obj = Basic.__new__(Intersection, self, other)
        return obj
                    
    def __add__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Add
        other = sympify(other)
        if other.is_Number:
            self, other = other, self
        return Basic.__new__(Add, self, other)

    def __radd__(self, lhs):
        from sympy.core.of import Basic, sympify
        from sympy import Add
        lhs = sympify(lhs)
        return Basic.__new__(Add, lhs, self)
    
    def __mul__(self, other):
        from sympy.core.of import Basic
        return Basic.__mul__(self, other)

    def __rmul__(self, lhs):
        from sympy.core.of import Basic, sympify
        from sympy import Mul
        return Basic.__new__(Mul, sympify(lhs), self)
    
    def __matmul__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import MatMul
        other = sympify(other)
        return Basic.__new__(MatMul, self, other)
    
    def __rmatmul__(self, lhs):
        from sympy.core.of import Basic
        return Basic.__matmul__(lhs, self)
    
    def __sub__(self, other):
        from sympy.core.of import Basic
        return Basic.__sub__(self, other)

    def __rsub__(self, lhs):
        from sympy.core.of import Basic, sympify
        lhs = sympify(lhs)
        return Basic.__sub__(lhs, self)

    def __neg__(self):
        from sympy.core.of import Basic
        from sympy import Mul, S
        if self.is_Mul:
            return Basic.__new__(Mul, S.NegativeOne)
        return Basic.__new__(Mul, S.NegativeOne, self)
    
    def __invert__(self):
        return Wanted(self)
    
    def __floordiv__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Floor
        other = sympify(other)
        return Basic.__new__(Floor, self / other)
        
    def __truediv__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Mul, Pow, S
        other = sympify(other)
        if other.is_Integer:
            other = 1 / other
            self, other = other, self
        else:
            if other.is_Pow:
                b, e = other.args
                other = Basic.__new__(Pow, b, -e)
            else:
                other = Basic.__new__(Pow, other, S.NegativeOne)
        return Basic.__new__(Mul, self, other)

#     lhs / self
    def __rtruediv__(self, lhs):
        from sympy.core.of import Basic, sympify
        from sympy import Mul, Pow, S
        lhs = sympify(lhs)
        
        pow = Basic.__new__(Pow, self, S.NegativeOne)
        if lhs == 1:
            return pow                    
        return Basic.__new__(Mul, lhs, pow)

    def __mod__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Mod
        other = sympify(other)
        return Basic.__new__(Mod, self, other)

    def __pow__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Pow
        other = sympify(other)
                    
        return Basic.__new__(Pow, self, other)

    def __rpow__(self, lhs):
        from sympy.core.of import Basic, sympify
        from sympy import Pow
        lhs = sympify(lhs)
        return Basic.__new__(Pow, lhs, self)
    
    def __gt__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Greater
        other = sympify(other)
        return Basic.__new__(Greater, self, other)

    def __ge__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import GreaterEqual
        other = sympify(other)
        return Basic.__new__(GreaterEqual, self, other)

    def __lt__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Less
        other = sympify(other)
        return Basic.__new__(Less, self, other)

    def __le__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import LessEqual
        other = sympify(other)
        return Basic.__new__(LessEqual, self, other)
    
    # self < other
    def __lshift__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Assuming
        other = sympify(other)
        return Basic.__new__(Assuming, self, other)

    # self > other
    def __rshift__(self, other):
        from sympy.core.of import Basic, sympify
        from sympy import Infer
        other = sympify(other)
        return Basic.__new__(Infer, self, other)
    
    @property
    @cacheit
    def is_abstract(self):
        return bool(self.__subclasses__())


class Wanted:
    is_Wanted = True
    
    def __str__(self):
        func = self.func
        if isinstance(func, type):
            return func.__name__
        return str(func)
    
    __repr__ = __str__
    
    def __init__(self, func):
        self.func = func
        
    def __getattr__(self, attr):
        return getattr(self.func, attr)
    
    def __invert__(self):
        # is wanted again?
        return self
    
    def is_wanted(self):
        return True

    __add__ = BasicMeta.__add__
    __radd__ = BasicMeta.__radd__
    
    __sub__ = BasicMeta.__sub__
    __rsub__ = BasicMeta.__rsub__
    
    __neg__ = BasicMeta.__neg__
    
    __mul__ = BasicMeta.__mul__
    __rmul__ = BasicMeta.__rmul__
    
    __truediv__ = BasicMeta.__truediv__
    __rtruediv__ = BasicMeta.__rtruediv__
    
    __pow__ = BasicMeta.__pow__
    
    __and__ = BasicMeta.__and__
    __or__ = BasicMeta.__or__
    
    __gt__ = BasicMeta.__gt__
    __ge__ = BasicMeta.__ge__
    __lt__ = BasicMeta.__lt__
    __le__ = BasicMeta.__le__
