from sympy.core import Expr
from sympy.core.decorators import call_highest_priority, _sympifyit
from sympy.sets import ImageSet
from sympy.sets.sets import set_add, set_sub, set_mul, set_div, set_pow, set_function
from sympy.core.function import Function

class SetExpr(Expr):
    """An expression that can take on values of a set

    >>> from sympy import Interval, FiniteSet
    >>> from sympy.sets.setexpr import SetExpr

    >>> a = SetExpr(Interval(0, 5))
    >>> b = SetExpr(FiniteSet(1, 10))
    >>> (a + b).set
    Union(Interval(1, 6), Interval(10, 15))
    >>> (2*a + b).set
    Interval(1, 20)
    """
    _op_priority = 11.0

    def __new__(cls, setarg):
        return Expr.__new__(cls, setarg)

    set = property(lambda self: self.args[0])

    def _latex(self, printer):
        return r"SetExpr\left({0}\right)".format(printer._print(self.set))

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__radd__')
    def __add__(self, other):
        return _setexpr_apply_operation(set_add, self, other)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__add__')
    def __radd__(self, other):
        return _setexpr_apply_operation(set_add, other, self)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rmul__')
    def __mul__(self, other):
        return _setexpr_apply_operation(set_mul, self, other)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__mul__')
    def __rmul__(self, other):
        return _setexpr_apply_operation(set_mul, other, self)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rsub__')
    def __sub__(self, other):
        return _setexpr_apply_operation(set_sub, self, other)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__sub__')
    def __rsub__(self, other):
        return _setexpr_apply_operation(set_sub, other, self)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rpow__')
    def __pow__(self, other):
        return _setexpr_apply_operation(set_pow, self, other)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__pow__')
    def __rpow__(self, other):
        return _setexpr_apply_operation(set_pow, other, self)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__rdiv__')
    def __div__(self, other):
        return _setexpr_apply_operation(set_div, self, other)

    @_sympifyit('other', NotImplemented)
    @call_highest_priority('__div__')
    def __rdiv__(self, other):
        return _setexpr_apply_operation(set_div, other, self)

    __truediv__ = __div__
    __rtruediv__ = __rdiv__

    def _eval_func(self, func):
        # TODO: this could be implemented straight into `imageset`:
        res = set_function(func, self.set)
        if res is None:
            return SetExpr(ImageSet(func, self.set))
        return SetExpr(res)
    
    def _eval_exp(self):
        from sympy import exp
        return self._eval_func(exp)

def _setexpr_apply_operation(op, x, y):
    if isinstance(x, SetExpr):
        x = x.set
    if isinstance(y, SetExpr):
        y = y.set
    out = op(x, y)
    return SetExpr(out)


class Card(Function):
    """
    We use the notation |A| to refer to the cardinality of a set A; that is,
        |A| = number of elements in A .
    """

    is_extended_integer = True
    is_extended_negative = False

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.integer(nonnegative=True)

    def fdiff(self, argindex=1):
        """
        Get the first derivative of the argument to Abs().

        Examples
        ========

        >>> from sympy.abc import x
        >>> from sympy.functions import Abs
        >>> Abs(-x).fdiff()
        sign(x)
        """
        if argindex == 1:
            return sign(self.args[0])
        else:
            raise ArgumentIndexError(self, argindex)

    @classmethod
    def eval(cls, arg):
        return arg._eval_Card()
        
        
    def _eval_is_integer(self):
        if self.arg.is_finiteset:
            return True

    def _eval_is_zero(self):
        return self._args[0].is_zero

    def _eval_is_extended_positive(self):
        is_z = self.is_zero
        if is_z is not None:
            return not is_z

    def _eval_is_rational(self):
        if self.arg.is_set:
            return True                
        return self.args[0].is_rational

    def _eval_is_finite(self):
        return self.arg.is_finiteset

    def _eval_is_even(self):
        if self.args[0].is_extended_real:
            return self.args[0].is_even

    def _eval_is_algebraic(self):
        return self.args[0].is_algebraic

    def _eval_power(self, exponent):
        x = self.args[0]
        if x.is_extended_real and exponent.is_integer:
            if exponent.is_even:
                return x ** exponent
            elif not exponent.is_NegativeOne and exponent.is_Integer:
                return x ** (exponent - 1) * self
        elif exponent.is_Rational:
            q = exponent.q
            if x.is_Pow:
                b, e = x.args
                if not e % q: 
                    x = b ** (e / q)
                    return abs(x) ** exponent.p
            elif x.is_Mul:
                args = []
                for t in x.args:
                    if not t.is_Pow:
                        break
                    b, e = t.args
                    if e % q:
                        break
                    
                    t = b ** (e / q)
                    args.append(t)
                else:
                    x = Mul(*args)
                    return abs(x) ** exponent.p 
        return

    def _eval_nseries(self, x, n, logx):
        direction = self.args[0].leadterm(x)[0]
        s = self.args[0]._eval_nseries(x, n=n, logx=logx)
        when = Eq(direction, 0)
        return Piecewise(
            ((s.subs(direction, 0)), when),
            (sign(direction) * s, True),
        )

    def _sage_(self):
        import sage.all as sage
        return sage.abs_symbolic(self.args[0]._sage_())

    def _eval_derivative(self, x):
        if self.args[0].is_extended_real or self.args[0].is_imaginary:
            return Derivative(self.args[0], x, evaluate=True) \
                * sign(conjugate(self.args[0]))
        rv = (Re(self.args[0]) * Derivative(Re(self.args[0]), x,
            evaluate=True) + Im(self.args[0]) * Derivative(Im(self.args[0]),
                x, evaluate=True)) / Abs(self.args[0])
        return rv.rewrite(sign)

    def _eval_rewrite_as_Heaviside(self, arg, **kwargs):
        # Note this only holds for real arg (since Heaviside is not defined
        # for complex arguments).
        from sympy.functions.special.delta_functions import Heaviside
        if arg.is_extended_real:
            return arg * (Heaviside(arg) - Heaviside(-arg))

    def _eval_rewrite_as_Piecewise(self, arg, **kwargs):
        if arg.is_extended_real:
            return Piecewise((arg, arg >= 0), (-arg, True))

    def _eval_rewrite_as_sign(self, arg, **kwargs):
        return arg / sign(arg)

    def min(self):
        x = self.arg
        if not x.is_set:
            if x >= 0:
                return x.min()
            if x <= 0:
                return abs(x.max())
        return S.Zero
    
    def _sympystr(self, p):
        return "|%s|" % p._print(self.arg)
    
    def _latex(self, p, exp=None):
        tex = r"\left|{%s}\right|" % p._print(self.args[0])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex

class Measure(Function):
    """
    Return the absolute value of the argument.

    This is an extension of the built-in function abs() to accept symbolic
    values.  If you pass a SymPy expression to the built-in abs(), it will
    pass it automatically to Abs().

    Examples
    ========

    >>> from sympy import Abs, Symbol, S
    >>> Abs(-1)
    1
    >>> x = Symbol('x', real=True)
    >>> Abs(-x)
    Abs(x)
    >>> Abs(x**2)
    x**2
    >>> abs(-x) # The Python built-in
    Abs(x)

    Note that the Python built-in will return either an Expr or int depending on
    the argument::

        >>> type(abs(-1))
        <... 'int'>
        >>> type(abs(S.NegativeOne))
        <class 'sympy.core.numbers.One'>

    Abs will always return a sympy object.

    See Also
    ========

    sign, conjugate
    """

    is_extended_real = True
    is_extended_negative = False
    is_extended_nonnegative = True
    unbranched = True

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        if self.arg.is_set:
            return dtype.integer(nonnegative=True)
        return dtype.real(nonnegative=True)

    def fdiff(self, argindex=1):
        """
        Get the first derivative of the argument to Abs().

        Examples
        ========

        >>> from sympy.abc import x
        >>> from sympy.functions import Abs
        >>> Abs(-x).fdiff()
        sign(x)
        """
        if argindex == 1:
            return sign(self.args[0])
        else:
            raise ArgumentIndexError(self, argindex)

    @classmethod
    def eval(cls, arg):
        ...
        
    def _eval_is_zero(self):
        return self._args[0].is_zero

    def _eval_is_extended_positive(self):
        is_z = self.is_zero
        if is_z is not None:
            return not is_z

    def _eval_is_rational(self):
        if self.arg.is_set:
            return True                
        return self.args[0].is_rational

    def _eval_is_finite(self):
        return self.arg.is_finite

    def _eval_is_even(self):
        if self.args[0].is_extended_real:
            return self.args[0].is_even

    def _eval_is_algebraic(self):
        return self.args[0].is_algebraic

    def _eval_power(self, exponent):
        x = self.args[0]
        if x.is_extended_real and exponent.is_integer:
            if exponent.is_even:
                return x ** exponent
            elif exponent is not S.NegativeOne and exponent.is_Integer:
                return x ** (exponent - 1) * self
        elif exponent.is_Rational:
            q = exponent.q
            if x.is_Pow:
                b, e = x.args
                if not e % q: 
                    x = b ** (e / q)
                    return abs(x) ** exponent.p
            elif x.is_Mul:
                args = []
                for t in x.args:
                    if not t.is_Pow:
                        break
                    b, e = t.args
                    if e % q:
                        break
                    
                    t = b ** (e / q)
                    args.append(t)
                else:
                    x = Mul(*args)
                    return abs(x) ** exponent.p 
        return

    def _eval_nseries(self, x, n, logx):
        direction = self.args[0].leadterm(x)[0]
        s = self.args[0]._eval_nseries(x, n=n, logx=logx)
        when = Eq(direction, 0)
        return Piecewise(
            ((s.subs(direction, 0)), when),
            (sign(direction) * s, True),
        )

    def _sage_(self):
        import sage.all as sage
        return sage.abs_symbolic(self.args[0]._sage_())

    def _eval_derivative(self, x):
        if self.args[0].is_extended_real or self.args[0].is_imaginary:
            return Derivative(self.args[0], x, evaluate=True) \
                * sign(conjugate(self.args[0]))
        rv = (Re(self.args[0]) * Derivative(Re(self.args[0]), x,
            evaluate=True) + Im(self.args[0]) * Derivative(Im(self.args[0]),
                x, evaluate=True)) / Abs(self.args[0])
        return rv.rewrite(sign)

    def _eval_rewrite_as_Heaviside(self, arg, **kwargs):
        # Note this only holds for real arg (since Heaviside is not defined
        # for complex arguments).
        from sympy.functions.special.delta_functions import Heaviside
        if arg.is_extended_real:
            return arg * (Heaviside(arg) - Heaviside(-arg))

    def _eval_rewrite_as_Piecewise(self, arg, **kwargs):
        if arg.is_extended_real:
            return Piecewise((arg, arg >= 0), (-arg, True))

    def _eval_rewrite_as_sign(self, arg, **kwargs):
        return arg / sign(arg)

    def min(self):
        x = self.arg
        if not x.is_set:
            if x >= 0:
                return x.min()
            if x <= 0:
                return abs(x.max())
        return S.Zero
    
    def _sympystr(self, p):
        return "\N{GREEK SMALL LETTER MU}(%s)" % p._print(self.arg)
    
    def _latex(self, p, exp=None):
        # tex = r"\boldsymbol\mu\left({%s}\right)" % p._print(self.arg)
        # tex = r"\mathbf\mu\left({%s}\right)" % p._print(self.arg)
        tex = r"{\color{blue} \mu}\left({%s}\right)" % p._print(self.arg)
        
        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex
