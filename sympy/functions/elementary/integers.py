from sympy import Basic, Expr

from sympy.core import Add, S
from sympy.core.evalf import get_integer_part, PrecisionExhausted
from sympy.core.function import Function
from sympy.core.logic import fuzzy_or
from sympy.core.numbers import Integer
from sympy.core.relational import Gt, Lt, Ge, Le, Relational, is_eq
from sympy.core.symbol import Symbol
from sympy.core.sympify import _sympify
from sympy.multipledispatch import dispatch

###############################################################################
######################### FLOOR and CEILING FUNCTIONS #########################
###############################################################################


class RoundFunction(Function):
    """The base class for rounding functions."""

    @classmethod
    def eval(cls, arg):
        from sympy import Im
        v = cls._eval_number(arg)
        if v is not None:
            return v

        if arg.is_extended_integer or arg.is_finite == False:
            if arg.is_infinitesimal is None:
                return arg
        if arg.is_imaginary or (S.ImaginaryUnit * arg).is_real:
            i = Im(arg)
            if not i.has(S.ImaginaryUnit):
                return cls(i) * S.ImaginaryUnit
            return cls(arg, evaluate=False)

        # Integral, numerical, symbolic part
        ipart = npart = spart = S.Zero

        # Extract integral (or complex integral) terms
        terms = Add.make_args(arg)

        for t in terms:
            if t.is_integer or (t.is_imaginary and Im(t).is_integer):
                ipart += t
            elif t.has(Symbol):
                spart += t
            else:
                npart += t

        if not (npart or spart):
            return ipart

        # Evaluate npart numerically if independent of spart
        if npart and (
            not spart or
            npart.is_real and (spart.is_imaginary or (S.ImaginaryUnit * spart).is_real) or
                npart.is_imaginary and spart.is_real):
            try:
                r, i = get_integer_part(
                    npart, cls._dir, {}, return_ints=True)
                ipart += Integer(r) + Integer(i) * S.ImaginaryUnit
                npart = S.Zero
            except (PrecisionExhausted, NotImplementedError):
                pass

        spart += npart
        if not spart:
            return ipart
        elif spart.is_imaginary or (S.ImaginaryUnit * spart).is_real:
            return ipart + cls(Im(spart), evaluate=False) * S.ImaginaryUnit
        elif isinstance(spart, (floor, ceiling)):
            return ipart + spart
        else:
            return ipart + cls(spart, evaluate=False)

    def _eval_is_finite(self):
        return self.args[0].is_finite

    def _eval_is_extended_real(self):
        return self.args[0].is_extended_real

    def _eval_is_extended_integer(self):
        return self.args[0].is_extended_real

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        if self.is_finite:
            return dtype.integer
        else:
            return dtype.extended_integer

    def __iter__(self):
        raise TypeError
    
    def __getitem__(self, indices):
        from sympy.core.operations import AssocOp
        return AssocOp.getitem(self, indices)


class Floor(RoundFunction):
    """
    Floor is a univariate function which returns the largest integer
    value not greater than its argument. This implementation
    generalizes floor to complex numbers by taking the floor of the
    real and imaginary parts separately.

    Examples
    ========

    >>> from sympy import floor, E, I, S, Float, Rational
    >>> floor(17)
    17
    >>> floor(Rational(23, 10))
    2
    >>> floor(2*E)
    5
    >>> floor(-Float(0.567))
    -1
    >>> floor(-I/2)
    -I
    >>> floor(S(5)/2 + 5*I/2)
    2 + 2*I

    See Also
    ========

    sympy.functions.elementary.integers.ceiling

    References
    ==========

    .. [1] "Concrete mathematics" by Graham, pp. 87
    .. [2] http://mathworld.wolfram.com/FloorFunction.html

    """
    _dir = -1

    @classmethod
    def _eval_number(cls, arg):
        if arg.is_Number:
            return arg.floor()
        elif any(isinstance(i, j)
                for i in (arg, -arg) for j in (floor, ceiling)):
            return arg
        if arg.is_NumberSymbol:
            return arg.approximation_interval(Integer)[0]

        if arg.is_infinitesimal is not None:
            *args, infinitesimal = arg.args
            arg = Add(*args)
            if arg.is_integer:
                if infinitesimal.is_positive:
                    return arg
                return arg - 1
            return floor._eval_number(cls, arg)

    def _eval_nseries(self, x, n, logx, cdir=0):
        r = self.subs(x, 0)
        args = self.args[0]
        args0 = args.subs(x, 0)
        if args0 == r:
            direction = (args - args0).leadterm(x)[0]
            if direction.is_positive:
                return r
            else:
                return r - 1
        else:
            return r

    def _eval_is_extended_negative(self):
        return self.args[0].is_extended_negative
    
    def _eval_rewrite_as_ceiling(self, arg, **kwargs):
        return -ceiling(-arg)

    def _eval_rewrite_as_frac(self, arg, **kwargs):
        return arg - frac(arg)

    def _eval_Eq(self, other):
        if isinstance(self, floor):
            if (self.rewrite(ceiling) == other) or \
                    (self.rewrite(frac) == other):
                return S.true

    def __le__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                if other.is_Floor:
                    if self.arg <= other.arg:
                        return S.true
                return self.args[0] < other + 1
            if other.is_number and other.is_real:
                return self.args[0] < ceiling(other)
        if self.args[0] == other and other.is_real:
            return S.true
        if other is S.Infinity and self.is_finite:
            return S.true

        return Le(self, other, evaluate=False)

    def __ge__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                if other.is_Floor:
                    if self.arg >= other.arg:
                        return S.true
                return self.args[0] >= other
            if other.is_number and other.is_real:
                return self.args[0] >= ceiling(other)
        if self.args[0] == other and other.is_real:
            return S.false
        if other is S.NegativeInfinity and self.is_finite:
            return S.true

        return Ge(self, other, evaluate=False)

    def __gt__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                return self.args[0] >= other + 1
            if other.is_number and other.is_real:
                return self.args[0] >= ceiling(other)
        if self.args[0] == other and other.is_real:
            return S.false
        if other is S.NegativeInfinity and self.is_finite:
            return S.true

        return Gt(self, other, evaluate=False)

    def __lt__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                return self.args[0] < other
            if other.is_number and other.is_real:
                return self.args[0] < ceiling(other)
        if other is S.Infinity and self.is_finite:
            return S.true

        return Lt(self, other, evaluate=False)

    def _sympystr(self, p):
        return '\N{left floor}%s\N{right floor}' % p._print(self.arg)        
    
    def _latex(self, p, exp=None):
        tex = r"\left\lfloor{%s}\right\rfloor" % p._print(self.args[0])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex


floor = Floor


@dispatch(floor, Expr)
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return is_eq(lhs.rewrite(ceiling), rhs) or \
        is_eq(lhs.rewrite(frac), rhs)


class Ceiling(RoundFunction):
    """
    Ceiling is a univariate function which returns the smallest integer
    value not less than its argument. This implementation
    generalizes ceiling to complex numbers by taking the ceiling of the
    real and imaginary parts separately.

    Examples
    ========

    >>> from sympy import ceiling, E, I, S, Float, Rational
    >>> ceiling(17)
    17
    >>> ceiling(Rational(23, 10))
    3
    >>> ceiling(2*E)
    6
    >>> ceiling(-Float(0.567))
    0
    >>> ceiling(I/2)
    I
    >>> ceiling(S(5)/2 + 5*I/2)
    3 + 3*I

    See Also
    ========

    sympy.functions.elementary.integers.floor

    References
    ==========

    .. [1] "Concrete mathematics" by Graham, pp. 87
    .. [2] http://mathworld.wolfram.com/CeilingFunction.html

    """
    _dir = 1

    @classmethod
    def _eval_number(cls, arg):
        if arg.is_Number:
            return arg.ceiling()
        elif any(isinstance(i, j)
                for i in (arg, -arg) for j in (floor, ceiling)):
            return arg
        if arg.is_NumberSymbol:
            return arg.approximation_interval(Integer)[1]

    def _eval_nseries(self, x, n, logx, cdir=0):
        r = self.subs(x, 0)
        args = self.args[0]
        args0 = args.subs(x, 0)
        if args0 == r:
            direction = (args - args0).leadterm(x)[0]
            if direction.is_positive:
                return r + 1
            else:
                return r
        else:
            return r

    def _eval_is_extended_positive(self):
        return self.args[0].is_extended_positive

    def _eval_Eq(self, other):
        if isinstance(self, ceiling):
            if (self.rewrite(floor) == other) or \
                    (self.rewrite(frac) == other):
                return S.true

    def __lt__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                return self.args[0] <= other - 1
            if other.is_number and other.is_real:
                return self.args[0] <= floor(other)
        if self.args[0] == other and other.is_real:
            return S.false
        if other is S.Infinity and self.is_finite:
            return S.true

        return Lt(self, other, evaluate=False)

    def __gt__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                return self.args[0] > other
            if other.is_number and other.is_real:
                return self.args[0] > floor(other)
        if other is S.NegativeInfinity and self.is_finite:
            return S.true

        return Gt(self, other, evaluate=False)

    def __ge__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                if other.is_Ceiling:
                    if self.arg >= other.arg:
                        return S.true
                return self.args[0] > other - 1
            if other.is_number and other.is_real:
                return self.args[0] > floor(other)
        if self.args[0] == other and other.is_real:
            return S.true
        if other is S.NegativeInfinity and self.is_finite:
            return S.true

        return Ge(self, other, evaluate=False)

    def __le__(self, other):
        other = S(other)
        if self.args[0].is_real:
            if other.is_integer:
                if other.is_Ceiling:
                    if self.arg <= other.arg:
                        return S.true
                return self.args[0] <= other
            if other.is_number and other.is_real:
                return self.args[0] <= floor(other)
        if self.args[0] == other and other.is_real:
            return S.false
        if other is S.Infinity and self.is_finite:
            return S.true

        return Le(self, other, evaluate=False)

    def simplify(self, deep=False, **kwargs):
        arg = self.arg
        if arg.is_Mul:
            num, den = arg.as_numer_denom()
            if den.is_integer and num.is_integer:
                rem = num % den
                if rem.is_zero:
                    return arg
                if rem.is_zero == False:
                    return arg + (den - rem) / den
                
        return self

    def _sympystr(self, p):
        return '\N{left ceiling}%s\N{right ceiling}' % p._print(self.arg)        

    def _latex(self, p, exp=None):
        tex = r"\left\lceil{%s}\right\rceil" % p._print(self.args[0])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex


ceiling = Ceiling

        
@dispatch(ceiling, Basic)  # type:ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return is_eq(lhs.rewrite(floor), rhs) or is_eq(lhs.rewrite(frac), rhs)


class FractionalPart(Function):
    r"""Represents the fractional part of x

    For real numbers it is defined [1]_ as

    .. math::
        x - \left\lfloor{x}\right\rfloor

    Examples
    ========

    >>> from sympy import Symbol, frac, Rational, floor, I
    >>> frac(Rational(4, 3))
    1/3
    >>> frac(-Rational(4, 3))
    2/3

    returns zero for integer arguments

    >>> n = Symbol('n', integer=True)
    >>> frac(n)
    0

    rewrite as floor

    >>> x = Symbol('x')
    >>> frac(x).rewrite(floor)
    x - floor(x)

    for complex arguments

    >>> r = Symbol('r', real=True)
    >>> t = Symbol('t', real=True)
    >>> frac(t + I*r)
    I*frac(r) + frac(t)

    See Also
    ========

    sympy.functions.elementary.integers.floor
    sympy.functions.elementary.integers.ceiling

    References
    ===========

    .. [1] https://en.wikipedia.org/wiki/Fractional_part
    .. [2] http://mathworld.wolfram.com/FractionalPart.html

    """

    @classmethod
    def eval(cls, arg):
        from sympy import AccumBounds, Im

        def _eval(arg):
            if arg is S.Infinity or arg is S.NegativeInfinity:
                return AccumBounds(0, 1)
            if arg.is_integer:
                return S.Zero
            if arg.is_number:
                if arg is S.NaN:
                    return S.NaN
                elif arg is S.ComplexInfinity:
                    return S.NaN
                else:
                    return arg - floor(arg)
            return cls(arg, evaluate=False)

        terms = Add.make_args(arg)
        terms = [t for t in terms if not t.is_integer]
        real, imag = S.Zero, S.Zero
        for t in terms:
            # Two checks are needed for complex arguments
            # see issue-7649 for details
            if t.is_imaginary or (S.ImaginaryUnit * t).is_real:
                i = Im(t)
                if not i.has(S.ImaginaryUnit):
                    imag += i
                else:
                    real += t
            else:
                real += t

        real = _eval(real)
        imag = _eval(imag)
        return real + S.ImaginaryUnit * imag

    def _eval_is_finite(self):
        return True

    def _eval_is_extended_real(self):
        return self.args[0].is_extended_real
    
    def _eval_is_imaginary(self):
        return self.args[0].is_imaginary

    def _eval_is_integer(self):
        return self.args[0].is_integer

    def _eval_is_zero(self):
        return fuzzy_or([self.args[0].is_zero, self.args[0].is_integer])

    def _eval_is_negative(self):
        return False

    def __ge__(self, other):
        if self.is_extended_real:
            other = _sympify(other)
            # Check if other <= 0
            if other.is_extended_nonpositive:
                return S.true
            # Check if other >= 1
            res = self._value_one_or_more(other)
            if res is not None:
                return not(res)
        return Ge(self, other, evaluate=False)

    def __gt__(self, other):
        if self.is_extended_real:
            other = _sympify(other)
            # Check if other < 0
            res = self._value_one_or_more(other)
            if res is not None:
                return not(res)
            # Check if other >= 1
            if other.is_extended_negative:
                return S.true
        return Gt(self, other, evaluate=False)

    def __le__(self, other):
        if self.is_extended_real:
            other = _sympify(other)
            # Check if other < 0
            if other.is_extended_negative:
                return S.false
            # Check if other >= 1
            res = self._value_one_or_more(other)
            if res is not None:
                return res
        return Le(self, other, evaluate=False)

    def __lt__(self, other):
        if self.is_extended_real:
            other = _sympify(other)
            # Check if other <= 0
            if other.is_extended_nonpositive:
                return S.false
            # Check if other >= 1
            res = self._value_one_or_more(other)
            if res is not None:
                return res
        return Lt(self, other, evaluate=False)

    def _value_one_or_more(self, other):
        if other.is_extended_real:
            if other.is_number:
                res = other >= 1
                if res and not isinstance(res, Relational):
                    return S.true
            if other.is_integer and other.is_positive:
                return S.true

    def _latex(self, p, exp=None):
        tex = r"frac\left(%s\right)" % p._print(self.args[0])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex

    def _sympystr(self, p): 
        return "frac(%s)" % p._print(self.args[0])

        
frac = FractionalPart


@dispatch(frac, Basic)  # type:ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    if (lhs.rewrite(floor) == rhs) or \
        (lhs.rewrite(ceiling) == rhs):
        return True
    # Check if other < 0
    if rhs.is_extended_negative:
        return False
    # Check if other >= 1
    res = lhs._value_one_or_more(rhs)
    if res is not None:
        return False
