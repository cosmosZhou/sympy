from sympy.core import sympify
from sympy.core.add import Add
from sympy.core.cache import cacheit
from sympy.core.function import (Function, ArgumentIndexError, expand_mul)
from sympy.core.logic import fuzzy_and, fuzzy_not, fuzzy_or
from sympy.core.mul import Mul
from sympy.core.numbers import Integer, Rational
from sympy.core.power import Pow
from sympy.core.singleton import S
from sympy.core.symbol import Wild, Dummy
from sympy.functions.combinatorial.factorials import factorial
from sympy.ntheory import multiplicity, perfect_power

# NOTE IMPORTANT
# The series expansion code in this file is an important part of the gruntz
# algorithm for determining limits. _eval_nseries has to return a generalized
# power series with coefficients in C(log(x), log).
# In more detail, the result of _eval_nseries(self, x, n) must be
#   c_0*x**e_0 + ... (finitely many terms)
# where e_i are numbers (not necessarily integers) and c_i involve only
# numbers, the function log, and log(x). [This also means it must not contain
# log(x(1+p)), this *has* to be expanded to log(x)+log(1+p) if x.is_positive and
# p.is_positive.]


class ExpBase(Function):

    unbranched = True

    def __iter__(self):
        raise TypeError

    def __getitem__(self, index):
        return self.func(self.arg[index])

    def inverse(self, argindex=1):
        """
        Returns the inverse function of ``exp(x)``.
        """
        return log

    def as_numer_denom(self):
        """
        Returns this with a positive exponent as a 2-tuple (a fraction).

        Examples
        ========

        >>> from sympy.functions import exp
        >>> from sympy.abc import x
        >>> exp(-x).as_numer_denom()
        (1, exp(x))
        >>> exp(x).as_numer_denom()
        (exp(x), 1)
        """
        # this should be the same as Pow.as_numer_denom wrt
        # exponent handling
        exp = self.exp
        neg_exp = exp.is_negative
        if not neg_exp and not (-exp).is_negative:
            neg_exp = exp._coeff_isneg()
        if neg_exp:
            return S.One, self.func(-exp)
        return self, S.One

    @property
    def exp(self):
        """
        Returns the exponent of the function.
        """
        return self.args[0]

    def as_base_exp(self):
        """
        Returns the 2-tuple (base, exponent).
        """
        return self.func(1), Mul(*self.args)

    def _eval_conjugate(self):
        return self.func(self.arg.conjugate())

    def _eval_is_finite(self):
        arg = self.args[0]
        if arg.is_infinite:
            if arg.is_negative:
                return True
            if arg.is_positive:
                return False
        if arg.is_finite:
            return True

    def _eval_is_rational(self):
        s = self.func(*self.args)
        if s.func == self.func:
            if s.exp is S.Zero:
                return True
            elif s.exp.is_rational and fuzzy_not(s.exp.is_zero):
                return False
        else:
            return s.is_rational

    def _eval_is_zero(self):
        return (self.args[0] is S.NegativeInfinity)

    def _eval_power(self, other):
        """exp(arg)**e -> exp(arg*e) if assumptions allow it.
        """
        b, e = self.as_base_exp()
        return Pow._eval_power(Pow(b, e, evaluate=False), other)

    def _eval_expand_power_exp(self, **hints):
        arg = self.args[0]
#         if arg.is_Add and arg.is_commutative:
        if arg.is_Add:
            expr = 1
            for x in arg.args:
                expr *= self.func(x)
            return expr
        return self.func(arg)

    def _latex(self, p, exp=None):
        # TODO should exp_polar be printed differently? what about exp_polar(0), exp_polar(1)?
        tex = r"{\color{RoyalBlue} e}^{%s}" % p._print(self.args[0])
#         tex = r"\textcolor{blue} {e}^{%s}" % self._print(expr.args[0])
        return p._do_exponent(tex, exp)

class exp_polar(ExpBase):
    r"""
    Represent a 'polar number' (see g-function Sphinx documentation).

    Explanation
    ===========

    ``exp_polar`` represents the function
    `Exp: \mathbb{C} \rightarrow \mathcal{S}`, sending the complex number
    `z = a + bi` to the polar number `r = exp(a), \theta = b`. It is one of
    the main functions to construct polar numbers.

    Examples
    ========

    >>> from sympy import exp_polar, pi, I, exp

    The main difference is that polar numbers don't "wrap around" at `2 \pi`:

    >>> exp(2*pi*I)
    1
    >>> exp_polar(2*pi*I)
    exp_polar(2*I*pi)

    apart from that they behave mostly like classical complex numbers:

    >>> exp_polar(2)*exp_polar(3)
    exp_polar(5)

    See Also
    ========

    sympy.simplify.powsimp.powsimp
    polar_lift
    periodic_argument
    principal_branch
    """

    is_polar = True
    is_comparable = False  # cannot be evalf'd

    def _eval_Abs(self):   # Abs is never a polar number
        from sympy.functions.elementary.complexes import Re
        return exp(Re(self.args[0]))

    def _eval_evalf(self, prec):
        """ Careful! any evalf of polar numbers is flaky """
        from sympy import Im, pi, Re
        i = Im(self.args[0])
        try:
            bad = (i <= -pi or i > pi)
        except TypeError:
            bad = True
        if bad:
            return self  # cannot evalf for this argument
        res = exp(self.args[0])._eval_evalf(prec)
        if i > 0 and Im(res) < 0:
            # i ~ pi, but exp(I*i) evaluated to argument slightly bigger than pi
            return Re(res)
        return res

    def _eval_power(self, other):
        return self.func(self.args[0] * other)

    def _eval_is_extended_real(self):
        if self.args[0].is_extended_real:
            return True

    def as_base_exp(self):
        # XXX exp_polar(0) is special!
        if self.args[0] == 0:
            return self, S.One
        return ExpBase.as_base_exp(self)


class Exp(ExpBase):
    """
    The exponential function, :math:`e^x`.

    Examples
    ========

    >>> from sympy.functions import exp
    >>> from sympy.abc import x
    >>> from sympy import I, pi
    >>> exp(x)
    exp(x)
    >>> exp(x).diff(x)
    exp(x)
    >>> exp(I*pi)
    -1

    Parameters
    ==========

    arg : Expr

    See Also
    ========

    log
    """

    def fdiff(self, argindex=1):
        """
        Returns the first derivative of this function.
        """
        if argindex == 1:
            return self
        else:
            raise ArgumentIndexError(self, argindex)

    def _eval_refine(self, assumptions):
        from sympy.assumptions import ask, Q
        arg = self.args[0]
        if arg.is_Mul:
            Ioo = S.ImaginaryUnit * S.Infinity
            if arg in [Ioo, -Ioo]:
                return S.NaN

            coeff = arg.as_coefficient(S.Pi * S.ImaginaryUnit)
            if coeff:
                if ask(Q.integer(2 * coeff)):
                    if ask(Q.even(coeff)):
                        return S.One
                    elif ask(Q.odd(coeff)):
                        return S.NegativeOne
                    elif ask(Q.even(coeff + S.Half)):
                        return -S.ImaginaryUnit
                    elif ask(Q.odd(coeff + S.Half)):
                        return S.ImaginaryUnit

    @classmethod
    def eval(cls, arg):
        return arg._eval_exp()

    @property
    def base(self):
        """
        Returns the base of the exponential function.
        """
        return S.Exp1

    @staticmethod
    @cacheit
    def taylor_term(n, x, *previous_terms):
        """
        Calculates the next term in the Taylor series expansion.
        """
        if n < 0:
            return S.Zero
        if n == 0:
            return S.One
        x = sympify(x)
        if previous_terms:
            p = previous_terms[-1]
            if p is not None:
                return p * x / n
        return x ** n / factorial(n)

    def as_real_imag(self, deep=True, **hints):
        """
        Returns this function as a 2-tuple representing a complex number.

        Examples
        ========

        >>> from sympy import I
        >>> from sympy.abc import x
        >>> from sympy.functions import exp
        >>> exp(x).as_real_imag()
        (exp(re(x))*cos(im(x)), exp(re(x))*sin(im(x)))
        >>> exp(1).as_real_imag()
        (E, 0)
        >>> exp(I).as_real_imag()
        (cos(1), sin(1))
        >>> exp(1+I).as_real_imag()
        (E*cos(1), E*sin(1))

        See Also
        ========

        sympy.functions.elementary.complexes.re
        sympy.functions.elementary.complexes.im
        """
        import sympy
        re, im = self.args[0].as_real_imag()
        if deep:
            re = re.expand(deep, **hints)
            im = im.expand(deep, **hints)
        cos, sin = sympy.cos(im), sympy.sin(im)
        return exp(re) * cos, exp(re) * sin

    def _eval_subs(self, old, new, **hints):
        # keep processing of power-like args centralized in Pow
        if old.is_Pow:  # handle (exp(3*log(x))).subs(x**2, z) -> z**(3/2)
            old = exp(old.exp*log(old.base))
        elif old is S.Exp1 and new.is_Function:
            old = exp
        if isinstance(old, exp) or old is S.Exp1:
            f = lambda a: Pow(*a.as_base_exp(), evaluate=False) if (
                a.is_Pow or isinstance(a, exp)) else a
            return Pow._eval_subs(f(self), f(old), new)

        if old is exp and not new.is_Function:
            return new ** self.exp._subs(old, new)
        return Function._eval_subs(self, old, new)

    def _eval_is_extended_real(self):
        if self.args[0].is_extended_real:
            return True
        elif self.args[0].is_imaginary:
            arg2 = -S(2) * S.ImaginaryUnit * self.args[0] / S.Pi
            return arg2.is_even

    def _eval_is_algebraic(self):
        s = self.func(*self.args)
        if s.func == self.func:
            if fuzzy_not(self.exp.is_zero):
                if self.exp.is_algebraic:
                    return False
                elif (self.exp / S.Pi).is_rational:
                    return False
        else:
            return s.is_algebraic

    def _eval_is_extended_positive(self):
        if self.args[0].is_extended_real:
            return not self.args[0] is S.NegativeInfinity
        elif self.args[0].is_imaginary:
            arg2 = -S.ImaginaryUnit * self.args[0] / S.Pi
            return arg2.is_even

    def _eval_is_extended_negative(self):
        if self.arg.is_extended_real:
            return False
        
        if self.arg.is_imaginary:
            ...
        
    def _eval_nseries(self, x, n, logx, cdir=0):
        # NOTE Please see the comment at the beginning of this file, labelled
        #      IMPORTANT.
        from sympy import limit, oo, Order, powsimp
        arg = self.args[0]
        arg_series = arg._eval_nseries(x, n=n, logx=logx)
        if arg_series.is_Order:
            return 1 + arg_series
        arg0 = limit(arg_series.removeO(), x, 0)
        if arg0 in [-oo, oo]:
            return self
        t = Dummy("t")
        exp_series = exp(t)._taylor(t, n)
        o = exp_series.getO()
        exp_series = exp_series.removeO()
        r = exp(arg0) * exp_series.subs(t, arg_series - arg0)
        r += Order(o.expr.subs(t, (arg_series - arg0)), x)
        r = r.expand()
        return powsimp(r, deep=True, combine='exp')

    def _taylor(self, x, n):
        from sympy import Order
        l = []
        g = None
        for i in range(n):
            g = self.taylor_term(i, self.args[0], g)
            g = g.nseries(x, n=n)
            l.append(g)
        return Add(*l) + Order(x ** n, x)

    def _eval_as_leading_term(self, x, cdir=0):
        from sympy import Order
        arg = self.args[0]
        if arg.is_Add:
            return Mul(*[exp(f).as_leading_term(x) for f in arg.args])
        arg_1 = arg.as_leading_term(x)
        if Order(x, x).contains(arg_1):
            return S.One
        if Order(1, x).contains(arg_1):
            return exp(arg_1)
        ####################################################
        # The correct result here should be 'None'.        #
        # Indeed arg in not bounded as x tends to 0.       #
        # Consequently the series expansion does not admit #
        # the leading term.                                #
        # For compatibility reasons, the return value here #
        # is the original function, i.e. exp(arg),         #
        # instead of None.                                 #
        ####################################################
        return exp(arg)

    def _eval_rewrite_as_sin(self, arg, **kwargs):
        from sympy import sin
        I = S.ImaginaryUnit
        return sin(I * arg + S.Pi / 2) - I * sin(I * arg)

    def _eval_rewrite_as_cos(self, arg, **kwargs):
        from sympy import cos
        I = S.ImaginaryUnit
        return cos(I * arg) + I * cos(I * arg + S.Pi / 2)

    def _eval_rewrite_as_tanh(self, arg, **kwargs):
        from sympy import tanh
        return (1 + tanh(arg / 2)) / (1 - tanh(arg / 2))

    def _eval_rewrite_as_sqrt(self, arg, **kwargs):
        from sympy.functions.elementary.trigonometric import sin, cos
        if arg.is_Mul:
            coeff = arg.coeff(S.Pi * S.ImaginaryUnit)
            if coeff and coeff.is_number:
                cosine, sine = cos(S.Pi * coeff), sin(S.Pi * coeff)
                if not isinstance(cosine, cos) and not isinstance (sine, sin):
                    return cosine + S.ImaginaryUnit * sine

    def _eval_rewrite_as_Pow(self, arg, **kwargs):
        if arg.is_Mul:
            logs = [a for a in arg.args if isinstance(a, log) and len(a.args) == 1]
            if logs:
                return Pow(logs[0].args[0], arg.coeff(logs[0]))

    def domain_nonzero(self, x):
        from sympy import Interval, Range, oo
        if x.is_integer:
            return Range(-oo, oo)
        else:
            return Interval(-oo, oo)

    def is_continuous_at(self, *args):
        return True
    
    def monotonicity(self, x):
        arg, monotonicity = self.arg.monotonicity(x)
        if arg is None:
            return None, 0
        return self.func(arg, evaluate=False), monotonicity

    @classmethod
    def _eval_simplify_Lamda(cls, self, squeeze=False):
        expr = self.expr
        arg, *limits = expr.args
        lamda = self.func(arg, *self.limits)
        _lamda = lamda.simplify()
        if lamda != _lamda:
            return expr.func(_lamda, *limits, evaluate=False)
             
        return self
           
    @classmethod
    def sub_class_key(cls):
        return 10

    def _eval_is_nonzero(self):
        if self.shape:
            zero = self.is_zero
            if zero:
                return False
            if zero == False:
                return self.is_complex
            
            return
            
        return ExpBase._eval_is_nonzero(self)


exp = Exp
    
def match_real_imag(expr):
    """
    Try to match expr with a + b*I for real a and b.

    ``match_real_imag`` returns a tuple containing the real and imaginary
    parts of expr or (None, None) if direct matching is not possible. Contrary
    to ``re()``, ``im()``, ``as_real_imag()``, this helper won't force things
    by returning expressions themselves containing ``re()`` or ``im()`` and it
    doesn't expand its argument either.

    """
    r_, i_ = expr.as_independent(S.ImaginaryUnit, as_Add=True)
    if i_ == 0 and r_.is_real:
        return (r_, i_)
    i_ = i_.as_coefficient(S.ImaginaryUnit)
    if i_ and i_.is_real and r_.is_real:
        return (r_, i_)
    else:
        return (None, None) # simpler to check for than None


class Log(Function):
    r"""
    The natural logarithm function `\ln(x)` or `\log(x)`.

    Explanation
    ===========

    Logarithms are taken with the natural base, `e`. To get
    a logarithm of a different base ``b``, use ``log(x, b)``,
    which is essentially short-hand for ``log(x)/log(b)``.

    ``log`` represents the principal branch of the natural
    logarithm. As such it has a branch cut along the negative
    real axis and returns values having a complex argument in
    `(-\pi, \pi]`.

    Examples
    ========

    >>> from sympy import log, sqrt, S, I
    >>> log(8, 2)
    3
    >>> log(S(8)/3, 2)
    -log(3)/log(2) + 3
    >>> log(-1 + I*sqrt(3))
    log(2) + 2*I*pi/3

    See Also
    ========

    exp
    """
    
    is_complex = True
    
    def fdiff(self, argindex=1):
        """
        Returns the first derivative of the function.
        """
        if argindex == 1:
            return 1 / self.args[0]
        else:
            raise ArgumentIndexError(self, argindex)

    def inverse(self, argindex=1):
        r"""
        Returns `e^x`, the inverse function of `\log(x)`.
        """
        return exp

    @classmethod
    def eval(cls, arg, base=None):
        from sympy import unpolarify
        from sympy.calculus import AccumBounds
        from sympy.sets.setexpr import SetExpr
        from sympy.functions.elementary.complexes import Abs

        arg = sympify(arg)

        if base is not None:
            base = sympify(base)
            if base == 1:
                if arg == 1:
                    return S.NaN
                else:
                    return S.ComplexInfinity
            try:
                # handle extraction of powers of the base now
                # or else expand_log in Mul would have to handle this
                n = multiplicity(base, arg)
                if n:
                    return n + log(arg / base**n) / log(base)
                else:
                    return log(arg) / log(base)
            except ValueError:
                pass
            if base is not S.Exp1:
                return cls(arg) / cls(base)
            else:
                return cls(arg)

        if arg.is_Number:
            if arg.is_zero:
                return S.ComplexInfinity
            elif arg is S.One:
                return S.Zero
            elif arg is S.Infinity:
                return S.Infinity
            elif arg is S.NegativeInfinity:
                return S.Infinity
            elif arg is S.NaN:
                return S.NaN
            elif arg.is_Rational and arg.p == 1:
                return -cls(arg.q)

        I = S.ImaginaryUnit
        if isinstance(arg, exp) and arg.args[0].is_extended_real:
            return arg.args[0]
        elif isinstance(arg, exp) and arg.args[0].is_number:
            r_, i_ = match_real_imag(arg.args[0])
            if i_ and i_.is_comparable:
                i_ %= 2*S.Pi
                if i_ > S.Pi:
                    i_ -= 2*S.Pi
                return r_ + expand_mul(i_ * I, deep=False)
        elif isinstance(arg, exp_polar):
            return unpolarify(arg.exp)
        elif isinstance(arg, AccumBounds):
            if arg.min.is_positive:
                return AccumBounds(log(arg.min), log(arg.max))
            else:
                return
        elif isinstance(arg, SetExpr):
            return arg._eval_func(cls)

        if arg.is_number:
            if arg.is_negative:
                return S.Pi * I + cls(-arg)
            elif arg is S.ComplexInfinity:
                return S.ComplexInfinity
            elif arg is S.Exp1:
                return S.One

        if arg.is_zero:
            return S.ComplexInfinity

        # don't autoexpand Pow or Mul (see the issue 3351):
        if not arg.is_Add:
            coeff = arg.as_coefficient(I)

            if coeff is not None:
                if coeff is S.Infinity:
                    return S.Infinity
                elif coeff is S.NegativeInfinity:
                    return S.Infinity
                elif coeff.is_Rational:
                    if coeff.is_nonnegative:
                        return S.Pi * I * S.Half + cls(coeff)
                    else:
                        return -S.Pi * I * S.Half + cls(-coeff)

        if arg.is_number and arg.is_algebraic:
            # Match arg = coeff*(r_ + i_*I) with coeff>0, r_ and i_ real.
            coeff, arg_ = arg.as_independent(I, as_Add=False)
            if coeff.is_negative:
                coeff *= -1
                arg_ *= -1
            arg_ = expand_mul(arg_, deep=False)
            r_, i_ = arg_.as_independent(I, as_Add=True)
            i_ = i_.as_coefficient(I)
            if coeff.is_real and i_ and i_.is_real and r_.is_real:
                if r_.is_zero:
                    if i_.is_positive:
                        return S.Pi * I * S.Half + cls(coeff * i_)
                    elif i_.is_negative:
                        return -S.Pi * I * S.Half + cls(coeff * -i_)
                else:
                    from sympy import ratsimp, sqrt
                    # Check for arguments involving rational multiples of pi
                    t = (i_/r_).cancel()
                    t1 = (-t).cancel()
                    atan_table = {
                        # first quadrant only
                        sqrt(3): S.Pi/3,
                        1: S.Pi/4,
                        sqrt(5 - 2*sqrt(5)): S.Pi/5,
                        sqrt(2)*sqrt(5 - sqrt(5))/(1 + sqrt(5)): S.Pi/5,
                        sqrt(5 + 2*sqrt(5)): S.Pi*Rational(2, 5),
                        sqrt(2)*sqrt(sqrt(5) + 5)/(-1 + sqrt(5)): S.Pi*Rational(2, 5),
                        sqrt(3)/3: S.Pi/6,
                        sqrt(2) - 1: S.Pi/8,
                        sqrt(2 - sqrt(2))/sqrt(sqrt(2) + 2): S.Pi/8,
                        sqrt(2) + 1: S.Pi*Rational(3, 8),
                        sqrt(sqrt(2) + 2)/sqrt(2 - sqrt(2)): S.Pi*Rational(3, 8),
                        sqrt(1 - 2*sqrt(5)/5): S.Pi/10,
                        (-sqrt(2) + sqrt(10))/(2*sqrt(sqrt(5) + 5)): S.Pi/10,
                        sqrt(1 + 2*sqrt(5)/5): S.Pi*Rational(3, 10),
                        (sqrt(2) + sqrt(10))/(2*sqrt(5 - sqrt(5))): S.Pi*Rational(3, 10),
                        2 - sqrt(3): S.Pi/12,
                        (-1 + sqrt(3))/(1 + sqrt(3)): S.Pi/12,
                        2 + sqrt(3): S.Pi*Rational(5, 12),
                        (1 + sqrt(3))/(-1 + sqrt(3)): S.Pi*Rational(5, 12)
                    }
                    if t in atan_table:
                        modulus = ratsimp(coeff * Abs(arg_))
                        if r_.is_positive:
                            return cls(modulus) + I * atan_table[t]
                        else:
                            return cls(modulus) + I * (atan_table[t] - S.Pi)
                    elif t1 in atan_table:
                        modulus = ratsimp(coeff * Abs(arg_))
                        if r_.is_positive:
                            return cls(modulus) + I * (-atan_table[t1])
                        else:
                            return cls(modulus) + I * (S.Pi - atan_table[t1])

    def as_base_exp(self):
        """
        Returns this function in the form (base, exponent).
        """
        return self, S.One

    @staticmethod
    @cacheit
    def taylor_term(n, x, *previous_terms):  # of log(1+x)
        r"""
        Returns the next term in the Taylor series expansion of `\log(1+x)`.
        """
        from sympy import powsimp
        if n < 0:
            return S.Zero
        x = sympify(x)
        if n == 0:
            return x
        if previous_terms:
            p = previous_terms[-1]
            if p is not None:
                return powsimp((-n) * p * x / (n + 1), deep=True, combine='exp')
        return (1 - 2 * (n % 2)) * x ** (n + 1) / (n + 1)

    def _eval_expand_log(self, deep=True, **hints):
        from sympy import unpolarify, expand_log
        from sympy.concrete import Sum, Product
        force = hints.get('force', False)
        if (len(self.args) == 2):
            return expand_log(self.func(*self.args), deep=deep, force=force)
        arg = self.args[0]
        if arg.is_Integer:
            # remove perfect powers
            p = perfect_power(int(arg))
            if p is not False:
                return p[1] * self.func(p[0])
        elif arg.is_Rational:
            return log(arg.p) - log(arg.q)
        elif arg.is_Mul:
            expr = []
            nonpos = []
            for x in arg.args:
                if force or x.is_positive or x.is_polar:
                    a = self.func(x)
                    if isinstance(a, log):
                        expr.append(self.func(x)._eval_expand_log(**hints))
                    else:
                        expr.append(a)
                elif x.is_negative:
                    a = self.func(-x)
                    expr.append(a)
                    nonpos.append(S.NegativeOne)
                else:
                    nonpos.append(x)
            return Add(*expr) + log(Mul(*nonpos))
        elif arg.is_Pow or isinstance(arg, exp):
            if force or (arg.exp.is_extended_real and (arg.base.is_positive or ((arg.exp + 1)
                .is_positive and (arg.exp - 1).is_nonpositive))) or arg.base.is_polar:
                b = arg.base
                e = arg.exp
                a = self.func(b)
                if isinstance(a, log):
                    return unpolarify(e) * a._eval_expand_log(**hints)
                else:
                    return unpolarify(e) * a
        elif isinstance(arg, Product):
            if arg.expr.is_positive:
                return Sum(log(arg.expr), *arg.limits)

        return self.func(arg)

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.simplify.simplify import expand_log, simplify, inversecombine
        if (len(self.args) == 2):
            return simplify(self.func(*self.args), ratio=ratio, measure=measure,
                            rational=rational, inverse=inverse)
        expr = self.func(simplify(self.args[0], ratio=ratio, measure=measure,
                         rational=rational, inverse=inverse))
        if inverse:
            expr = inversecombine(expr)
        expr = expand_log(expr, deep=True)
        return min([expr, self], key=measure)

    def as_real_imag(self, deep=True, **hints):
        """
        Returns this function as a complex coordinate.

        Examples
        ========

        >>> from sympy import I
        >>> from sympy.abc import x
        >>> from sympy.functions import log
        >>> log(x).as_real_imag()
        (log(Abs(x)), arg(x))
        >>> log(I).as_real_imag()
        (0, pi/2)
        >>> log(1 + I).as_real_imag()
        (log(sqrt(2)), pi/4)
        >>> log(I*x).as_real_imag()
        (log(Abs(x)), arg(I*x))

        """
        from sympy import Abs, arg
        if deep:
            abs = Abs(self.args[0].expand(deep, **hints))
            arg = arg(self.args[0].expand(deep, **hints))
        else:
            abs = Abs(self.args[0])
            arg = arg(self.args[0])
        if hints.get('log', False):  # Expand the log
            hints['complex'] = False
            return (log(abs).expand(deep, **hints), arg)
        else:
            return (log(abs), arg)

    def _eval_is_rational(self):
        s = self.func(*self.args)
        if s.func == self.func:
            if (self.args[0] - 1).is_zero:
                return True
            if s.args[0].is_rational and fuzzy_not((self.args[0] - 1).is_zero):
                return False
        else:
            return s.is_rational

    def _eval_is_algebraic(self):
        s = self.func(*self.args)
        if s.func == self.func:
            if (self.args[0] - 1).is_zero:
                return True
            elif fuzzy_not((self.args[0] - 1).is_zero):
                if self.args[0].is_algebraic:
                    return False
        else:
            return s.is_algebraic

    def _eval_is_extended_real(self):
#         self.arg is defined to be nonzero already! so it is only necessary to return is_extended_nonnegative， not is_extended_positive!!
        return self.arg.is_extended_nonnegative
#         return self.arg.is_extended_positive

    def _eval_is_finite(self):
        arg = self.args[0]
        if arg.is_zero:
            return False
        return arg.is_finite

    def _eval_is_extended_positive(self):
        return (self.args[0] - 1).is_extended_positive

    def _eval_is_zero(self):
        return (self.args[0] - 1).is_zero

    def _eval_is_extended_negative(self):
        return (self.args[0] - 1).is_extended_negative

    def _eval_nseries(self, x, n, logx):
        # NOTE Please see the comment at the beginning of this file, labelled
        #      IMPORTANT.
        from sympy import cancel, Order
        if not logx:
            logx = log(x)
        if self.args[0] == x:
            return logx
        arg = self.args[0]
        k, l = Wild("k"), Wild("l")
        r = arg.match(k * x ** l)
        if r is not None:
            k, l = r[k], r[l]
            if l != 0 and not l.has(x) and not k.has(x):
                r = log(k) + l * logx  # XXX true regardless of assumptions?
                return r

        # TODO new and probably slow
        s = self.args[0].nseries(x, n=n, logx=logx)
        while s.is_Order:
            n += 1
            s = self.args[0].nseries(x, n=n, logx=logx)
        a, b = s.leadterm(x)
        p = cancel(s / (a * x ** b) - 1)
        g = None
        l = []
        for i in range(n + 2):
            g = log.taylor_term(i, p, g)
            g = g.nseries(x, n=n, logx=logx)
            l.append(g)
        return log(a) + b * logx + Add(*l) + Order(p ** n, x)

    def _eval_as_leading_term(self, x, cdir=0):
        arg = self.args[0].as_leading_term(x)
        if arg is S.One:
            return (self.args[0] - 1).as_leading_term(x)
        return self.func(arg)
    
    def simplify(self, **_):
        arg = self.arg
        if arg.is_Exp:
            return arg.arg
        if arg.is_Mul:
            coeff = []
            exponent = []
            for e in arg.args:
                if e.is_Exp:
                    coeff.append(e.arg)
                else:
                    exponent.append(e)
            if coeff:
                return Add(*coeff) + self.func(Mul(*exponent)).simplify()
        elif arg.is_Pow:
            base, exponent = arg.args
            if exponent._coeff_isneg():
                exponent = -exponent
            arg = base ** exponent
            return -self.func(arg)

        return self

    def __iter__(self):
        raise TypeError

    def __getitem__(self, index):
        return self.func(self.arg[index])

    def _eval_exp(self):
        return self.args[0]

    def _latex(self, p):
        arg = p._print(self.arg)
        if self.arg.is_AssocOp or self.arg.is_MatMul:
            return r"\log \left(%s\right)" % arg
        return r"\log {%s}" % arg

    def domain_definition(self, **_):
        from sympy import Unequal
        arg = self.arg
        if arg.shape:
            indices, limits = arg.variables_with_limits()
            from sympy import ForAll
            return ForAll(Unequal(arg[tuple(indices)], 0), *limits)
        return Unequal(arg, 0)
    
    @cacheit
    def _eval_domain_defined(self, x, **kwargs):
        real = kwargs.get('real')
        arg = self.arg
        if x == arg:
            if real:
                from sympy import Interval, oo
                return x.domain & Interval(0, oo, left_open=True)
            else:
                return x.domain - {0}
            
        if real:
            return arg._eval_domain_defined(x, positive=True)
        else:
            return arg._eval_domain_defined(x, zero=False)
    
    @classmethod
    def sub_class_key(cls):
        return 11


log = Log


class LambertW(Function):
    r"""
    The Lambert W function `W(z)` is defined as the inverse
    function of `w \exp(w)` [1]_.

    In other words, the value of `W(z)` is such that `z = W(z) \exp(W(z))`
    for any complex number `z`.  The Lambert W function is a multivalued
    function with infinitely many branches `W_k(z)`, indexed by
    `k \in \mathbb{Z}`.  Each branch gives a different solution `w`
    of the equation `z = w \exp(w)`.

    The Lambert W function has two partially real branches: the
    principal branch (`k = 0`) is real for real `z > -1/e`, and the
    `k = -1` branch is real for `-1/e < z < 0`. All branches except
    `k = 0` have a logarithmic singularity at `z = 0`.

    Examples
    ========

    >>> from sympy import LambertW
    >>> LambertW(1.2)
    0.635564016364870
    >>> LambertW(1.2, -1).n()
    -1.34747534407696 - 4.41624341514535*I
    >>> LambertW(-1).is_real
    False

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Lambert_W_function
    """

    @classmethod
    def eval(cls, x, k=None):
        if k is S.Zero:
            return cls(x)
        elif k is None:
            k = S.Zero

        if k is S.Zero:
            if x is S.Zero:
                return S.Zero
            if x is S.Exp1:
                return S.One
            if x == -1 / S.Exp1:
                return S.NegativeOne
            if x == -log(2) / 2:
                return -log(2)
            if x is S.Infinity:
                return S.Infinity

        if fuzzy_not(k.is_zero):
            if x is S.Zero:
                return S.NegativeInfinity
        if k is S.NegativeOne:
            if x == -S.Pi / 2:
                return -S.ImaginaryUnit * S.Pi / 2
            elif x == -1 / S.Exp1:
                return S.NegativeOne
            elif x == -2 * exp(-2):
                return -Integer(2)

    def fdiff(self, argindex=1):
        """
        Return the first derivative of this function.
        """
        x = self.args[0]

        if len(self.args) == 1:
            if argindex == 1:
                return LambertW(x) / (x * (1 + LambertW(x)))
        else:
            k = self.args[1]
            if argindex == 1:
                return LambertW(x, k) / (x * (1 + LambertW(x, k)))

        raise ArgumentIndexError(self, argindex)

    def _eval_is_extended_real(self):
        x = self.args[0]
        if len(self.args) == 1:
            k = S.Zero
        else:
            k = self.args[1]
        if k.is_zero:
            if (x + 1 / S.Exp1).is_positive:
                return True
            elif (x + 1 / S.Exp1).is_nonpositive:
                return False
        elif (k + 1).is_zero:
            if x.is_negative and (x + 1 / S.Exp1).is_positive:
                return True
            elif x.is_nonpositive or (x + 1 / S.Exp1).is_nonnegative:
                return False
        elif fuzzy_not(k.is_zero) and fuzzy_not((k + 1).is_zero):
            if x.is_extended_real:
                return False

    def _eval_is_finite(self):
        return self.args[0].is_finite

    def _eval_is_algebraic(self):
        s = self.func(*self.args)
        if s.func == self.func:
            if fuzzy_not(self.args[0].is_zero) and self.args[0].is_algebraic:
                return False
        else:
            return s.is_algebraic
