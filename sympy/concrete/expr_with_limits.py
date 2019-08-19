from __future__ import print_function, division

from sympy.core.add import Add
from sympy.core.compatibility import is_sequence
from sympy.core.containers import Tuple
from sympy.core.expr import Expr
from sympy.core.mul import Mul
from sympy.core.relational import Equality, Relational
from sympy.core.singleton import S
from sympy.core.symbol import Symbol, Dummy
from sympy.core.sympify import sympify
from sympy.functions.elementary.piecewise import (piecewise_fold,
    Piecewise)
from sympy.logic.boolalg import BooleanFunction
from sympy.matrices import Matrix
from sympy.tensor.indexed import Idx
from sympy.sets.sets import Interval, Set, FiniteSet, Union, Complement, \
    EmptySet, Intersection
from sympy.sets.fancysets import Range
from sympy.utilities import flatten
from sympy.utilities.iterables import sift
from sympy.core.cache import cacheit
from sympy.functions.elementary.miscellaneous import Min, Max


def _common_new(cls, function, *symbols, **assumptions):
    """Return either a special return value or the tuple,
    (function, limits, orientation). This code is common to
    both ExprWithLimits and AddWithLimits."""
    function = sympify(function)
    if hasattr(function, 'func') and isinstance(function, Equality):
        lhs = function.lhs
        rhs = function.rhs
        return Equality(cls(lhs, *symbols, **assumptions), \
                        cls(rhs, *symbols, **assumptions))

    if function is S.NaN:
        return S.NaN

    if symbols:
        limits, orientation = _process_limits(*symbols)
        for i, li in enumerate(limits):
            if len(li) == 4:
                function = function.subs(li[0], li[-1])
                limits[i] = tuple(li[:-1])
    else:
        # symbol not provided -- we can still try to compute a general form
#         free = function.free_symbols
#         if len(free) != 1:
#             raise ValueError(
#                 "specify dummy variables for %s" % function)
#         limits, orientation = [Tuple(s) for s in free], 1
        limits, orientation = [], 1

    # denest any nested calls
    while cls == type(function):
        limits = list(function.limits) + limits
        function = function.function

    # Any embedded piecewise functions need to be brought out to the
    # top level. We only fold Piecewise that contain the integration
    # variable.
    reps = {}
    symbols_of_integration = set([i[0] for i in limits])
    for p in function.atoms(Piecewise):
        if not p.has(*symbols_of_integration):
            reps[p] = Dummy()
    # mask off those that don't
    function = function.xreplace(reps)
    # do the fold
    function = piecewise_fold(function)
    # remove the masking
    function = function.xreplace({v: k for k, v in reps.items()})

    return function, limits, orientation


def _process_limits(*symbols):
    """Process the list of symbols and convert them to canonical limits,
    storing them as Tuple(symbol, lower, upper). The orientation of
    the function is also returned when the upper limit is missing
    so (x, 1, None) becomes (x, None, 1) and the orientation is changed.
    """
    limits = []
    orientation = 1
    for V in symbols:
        if isinstance(V, (Relational, BooleanFunction)):
            variable = V.atoms(Symbol).pop()
            V = (variable, V.as_set())

        if isinstance(V, Symbol) or getattr(V, '_diff_wrt', False):
            if isinstance(V, Idx):
                if V.lower is None or V.upper is None:
                    limits.append(Tuple(V))
                else:
                    limits.append(Tuple(V, V.lower, V.upper))
            else:
                limits.append(Tuple(V))
            continue
        elif is_sequence(V, Tuple):
            if len(V) == 2 and isinstance(V[1], Range):
                lo = V[1].inf
                hi = V[1].sup
                dx = abs(V[1].step)
                V = [V[0]] + [0, (hi - lo) // dx, dx * V[0] + lo]
            V = sympify(flatten(V))  # a list of sympified elements
            if isinstance(V[0], (Symbol, Idx)) or getattr(V[0], '_diff_wrt', False):
                newsymbol = V[0]
                if len(V) == 2 and isinstance(V[1], Interval):  # 2 -> 3
                    # Interval
                    V[1:] = [V[1].start, V[1].end]
                elif len(V) == 3:
                    # general case
                    if V[2] is None and not V[1] is None:
                        orientation *= -1
                    V = [newsymbol] + [i for i in V[1:] if i is not None]

                if not isinstance(newsymbol, Idx) or len(V) == 3:
                    if len(V) == 4:
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 3:
                        if isinstance(newsymbol, Idx):
                            # Idx represents an integer which may have
                            # specified values it can take on; if it is
                            # given such a value, an error is raised here
                            # if the summation would try to give it a larger
                            # or smaller value than permitted. None and Symbolic
                            # values will not raise an error.
                            lo, hi = newsymbol.lower, newsymbol.upper
                            try:
                                if lo is not None and not bool(V[1] >= lo):
                                    raise ValueError("Summation will set Idx value too low.")
                            except TypeError:
                                pass
                            try:
                                if hi is not None and not bool(V[2] <= hi):
                                    raise ValueError("Summation will set Idx value too high.")
                            except TypeError:
                                pass
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 1 or (len(V) == 2 and V[1] is None):
                        limits.append(Tuple(newsymbol))
                        continue
                    elif len(V) == 2:
                        limits.append(Tuple(newsymbol, V[1]))
                        continue

        raise ValueError('Invalid limits given: %s' % str(symbols))

    return limits, orientation


class ExprWithLimits(Expr):
    __slots__ = ['is_commutative']

    def __new__(cls, function, *symbols, **assumptions):
        if cls in (Minimum, Maximum, Ref, UnionComprehension):
            if 'condition' in function.dtype.dict:
                lhs = function.lhs
                rhs = function.rhs
                return function.func(cls(lhs, *symbols, **assumptions), cls(rhs, *symbols, **assumptions))

            limits = [None] * len(symbols)
            for i, sym in enumerate(symbols):
                if isinstance(sym, Tuple):
                    limits[i] = sym
                elif isinstance(sym, tuple):
                    limits[i] = Tuple(*sym)
                else:
                    limits[i] = Tuple(sym,)
        else:
            pre = _common_new(cls, function, *symbols, **assumptions)
            if type(pre) is tuple:
                function, limits, _ = pre
            else:
                return pre

            # limits must have upper and lower bounds; the indefinite form
            # is not supported. This restriction does not apply to AddWithLimits
            if any(len(l) != 3 or None in l for l in limits):
                raise ValueError('ExprWithLimits requires values for lower and upper bounds.')

        obj = Expr.__new__(cls, **assumptions)
        arglist = [function]
        arglist.extend(limits)
        obj._args = tuple(arglist)
        obj.is_commutative = function.is_commutative  # limits already checked

        return obj

    @property
    def function(self):
        """Return the function applied across limits.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x
        >>> Integral(x**2, (x,)).function
        x**2

        See Also
        ========

        limits, variables, free_symbols
        """
        return self._args[0]

    @property
    def limits(self):
        """Return the limits of expression.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i
        >>> Integral(x**i, (i, 1, 3)).limits
        ((i, 1, 3),)

        See Also
        ========

        function, variables, free_symbols
        """
        return self._args[1:]

    @property
    def variables(self):
        """Return a list of the limit variables.

        >>> from sympy import Sum
        >>> from sympy.abc import x, i
        >>> Sum(x**i, (i, 1, 3)).variables
        [i]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return [l[0] for l in self.limits]

    @property
    def bound_symbols(self):
        """Return only variables that are dummy variables.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i, j, k
        >>> Integral(x**i, (i, 1, 3), (j, 2), k).bound_symbols
        [i, j]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return [l[0] for l in self.limits if len(l) != 1]

    @property
    def free_symbols(self):
        """
        This method returns the symbols in the object, excluding those
        that take on a specific value (i.e. the dummy symbols).

        Examples
        ========

        >>> from sympy import Sum
        >>> from sympy.abc import x, y
        >>> Sum(x, (x, y, 1)).free_symbols
        {y}
        """
        # don't test for any special values -- nominal free symbols
        # should be returned, e.g. don't return set() if the
        # function is zero -- treat it like an unevaluated expression.
        function, limits = self.function, self.limits
        isyms = function.free_symbols
        for xab in limits:
            if len(xab) == 1:
                isyms.add(xab[0])
                continue
            # take out the target symbol
            if xab[0] in isyms:
                isyms.remove(xab[0])
            # add in the new symbols
            for i in xab[1:]:
                isyms.update(i.free_symbols)
        return isyms

    @property
    def is_number(self):
        """Return True if the Sum has no free symbols, else False."""
        return not self.free_symbols

    def _eval_interval(self, x, a, b):
        limits = [(i if i[0] != x else (x, a, b)) for i in self.limits]
        integrand = self.function
        return self.func(integrand, *limits)

    def _eval_subs(self, old, new):
        """
        Perform substitutions over non-dummy variables
        of an expression with limits.  Also, can be used
        to specify point-evaluation of an abstract antiderivative.

        Examples
        ========

        >>> from sympy import Sum, oo
        >>> from sympy.abc import s, n
        >>> Sum(1/n**s, (n, 1, oo)).subs(s, 2)
        Sum(n**(-2), (n, 1, oo))

        >>> from sympy import Integral
        >>> from sympy.abc import x, a
        >>> Integral(a*x**2, x).subs(x, 4)
        Integral(a*x**2, (x, 4))

        See Also
        ========

        variables : Lists the integration variables
        transform : Perform mapping on the dummy variable for integrals
        change_index : Perform mapping on the sum and product dummy variables

        """
        from sympy.core.function import AppliedUndef, UndefinedFunction
        func, limits = self.function, list(self.limits)

        # If one of the expressions we are replacing is used as a func index
        # one of two things happens.
        #   - the old variable first appears as a free variable
        #     so we perform all free substitutions before it becomes
        #     a func index.
        #   - the old variable first appears as a func index, in
        #     which case we ignore.  See change_index.

        # Reorder limits to match standard mathematical practice for scoping
        limits.reverse()

        if not isinstance(old, Symbol) or \
                old.free_symbols.intersection(self.free_symbols):
            sub_into_func = True
            for i, xab in enumerate(limits):
                if 1 == len(xab) and old == xab[0]:
                    if new._diff_wrt:
                        xab = (new,)
                    else:
                        xab = (old, old)
                limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                if self.func.__name__ in ('Sum', 'Product', 'Integral'):
                    if len(xab[0].free_symbols.intersection(old.free_symbols)) != 0:
                        sub_into_func = False
                        break

            if isinstance(old, AppliedUndef) or isinstance(old, UndefinedFunction):
                sy2 = set(self.variables).intersection(set(new.atoms(Symbol)))
                sy1 = set(self.variables).intersection(set(old.args))
                if not sy2.issubset(sy1):
                    raise ValueError(
                        "substitution can not create dummy dependencies")
                sub_into_func = True
            if sub_into_func:
                func = func.subs(old, new)
        else:
            # old is a Symbol and a dummy variable of some limit
            for i, xab in enumerate(limits):
                if len(xab) == 3:
                    limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                    if old == xab[0]:
                        break
        # simplify redundant limits (x, x)  to (x, )
        for i, xab in enumerate(limits):
            if len(xab) == 2 and (xab[0] - xab[1]).is_zero:
                limits[i] = Tuple(xab[0],)

        # Reorder limits back to representation-form
        limits.reverse()

        return self.func(func, *limits)

    def as_multiple_terms(self, x, domain):
        univeralSet = Interval(S.NegativeInfinity, S.Infinity, integer=True)
        args = []
        union = S.EmptySet
        for f, condition in self.function.args:
            _domain = (univeralSet - union) & x.conditional_domain(condition) & domain
            union |= _domain

            if isinstance(_domain, FiniteSet):
                for e in _domain:
                    args.append(f.subs(x, e))
            elif _domain != S.EmptySet:
                assert _domain.is_integer
                if _domain.is_Interval:
                    args.append(self.func(f, (x, _domain.min(), _domain.max())).simplifier())
                else:
                    args.append(self.func(f, (x, _domain)).simplifier())

        return args

    def _subs(self, old, new):
        """Override this stub if you want to do anything more than
        attempt a replacement of old with new in the arguments of self.
        """
        from sympy.core.basic import _aresame
        if _aresame(self, old):
            return new

        from sympy.tensor.indexed import Slice
        if isinstance(old, Slice):
#             function = self.function
            rule = {}
            for limit in self.limits:
                x, *ab = limit
                if ab:
                    rule[x] = Symbol(x.name, domain=Interval(*ab, integer=True))
            function = self.function.subs(rule)
            _function = function.subs(old, new)
            if _function != function:
                function = _function.subs({v : k for k, v in rule.items()})
                return self.func(function, *self.limits)

        hit = False
        args = list(self.args)
        for i, arg in enumerate(args):
            if not hasattr(arg, '_eval_subs'):
                continue
            arg = arg._subs(old, new)

            if not _aresame(arg, args[i]):
                hit = True
                args[i] = arg
        if hit:
            rv = self.func(*args)
            return rv
        return self

    def bisect(self, front=None, back=None):
        (x, *_), *_ = self.limits
        from sympy.tensor.indexed import Slice
        if isinstance(x, Slice):
            z, x = x.bisect(front, back)
            return self.func(self.func(self.function, (x,)).simplifier(), (z,))
        return self

    def _has(self, pattern):
        """Helper for .has()"""
        from sympy.tensor.indexed import Indexed, Slice
        from sympy.core.assumptions import BasicMeta
        from sympy.core.function import UndefinedFunction
        if isinstance(pattern, (BasicMeta, UndefinedFunction)):
            return Expr._has(self, pattern)
        if not isinstance(pattern, (Symbol, Indexed, Slice)):
            return Expr._has(self, pattern)

        function = self.function
        limits = []

        if self.limits:
            for limit in self.limits:
                x, *args = limit
                if x == pattern:
                    return False

                if len(args) == 0:
                    limits.append(limit)
                elif len(args) == 1:
                    limits.append(limit)
                else:
                    a, b = args
                    _x = Symbol(x.name, integer=x.is_integer, domain=Interval(a, b))
                    function = function.subs(x, _x)
                    limits.append(Tuple(_x, a, b))

        boolean = function._has(pattern)

        return boolean or any(arg._has(pattern) for arg in limits)


class AddWithLimits(ExprWithLimits):
    r"""Represents unevaluated oriented additions.
        Parent class for Integral and Sum.
    """

    def __new__(cls, function, *symbols, **assumptions):
        pre = _common_new(cls, function, *symbols, **assumptions)
        if type(pre) is tuple:
            function, limits, orientation = pre
        else:
            return pre

        obj = Expr.__new__(cls, **assumptions)
        arglist = [orientation * function]  # orientation not used in ExprWithLimits
        arglist.extend(limits)
        obj._args = tuple(arglist)
        obj.is_commutative = function.is_commutative  # limits already checked

        return obj

    def _eval_adjoint(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.adjoint(), *self.limits)
        return None

    def _eval_conjugate(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.conjugate(), *self.limits)
        return None

    def _eval_transpose(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.transpose(), *self.limits)
        return None

    def _eval_factor(self, **hints):
        if 1 == len(self.limits):
            summand = self.function.factor(**hints)
            if summand.is_Mul:
                out = sift(summand.args, lambda w: w.is_commutative \
                    and not set(self.variables) & w.free_symbols)
                return Mul(*out[True]) * self.func(Mul(*out[False]), \
                    *self.limits)
        else:
            summand = self.func(self.function, *self.limits[0:-1]).factor()
            if not summand.has(self.variables[-1]):
                return self.func(1, [self.limits[-1]]).doit() * summand
            elif isinstance(summand, Mul):
                return self.func(summand, self.limits[-1]).factor()
        return self

    def _eval_expand_basic(self, **hints):
        summand = self.function.expand(**hints)
        if summand.is_Add and summand.is_commutative:
            return Add(*[self.func(i, *self.limits) for i in summand.args])
        elif summand.is_Matrix:
            return Matrix._new(summand.rows, summand.cols,
                [self.func(i, *self.limits) for i in summand._mat])
        elif summand != self.function:
            return self.func(summand, *self.limits)
        return self

    def as_multiple_limits(self):
        if isinstance(self.function, Mul):
            integral = []
            function = []
            for arg in self.function:
                if isinstance(arg, self.func):
                    integral.append(arg)
                else:
                    function.append(arg)
            if integral:
                limits = self.limits[:]
                for it in integral:
                    limits += it.limits
                    if isinstance(it.function, Mul):
                        function += it.function.args
                    else:
                        function.append(it.function)
                return self.func(Mul(*function), *limits)
        return self

    def as_separate_limits(self):
        if len(self.limits) < 2:
            return self
        limit = self.limits[0]
        if len(limit) == 1:
            function = self.func(self.function, *self.limits[1:]).as_separate_limits().simplifier()
            return self.func(function, limit)
        x, a, b = limit

        limits = []
        for i in range(1, len(self.limits)):
            t, *ab = self.limits[i]
            if ab:
                domain = Interval(*ab, integer=True)
            else:
                domain = Interval(-S.oo, S.oo, integer=True)

            if a.has(t):
                domain &= t.conditional_domain(a <= x)
                from sympy.functions.elementary.miscellaneous import Minimum
                a = Minimum(a, self.limits[i]).doit()
            if b.has(t):
                domain &= t.conditional_domain(x <= b)
                from sympy.functions.elementary.miscellaneous import Maximum
                b = Maximum(b, self.limits[i]).doit()

            limits.append((t, domain.start, domain.end))

        function = self.func(self.function, *limits).as_separate_limits().simplifier()
        return self.func(function, (x, a, b))


def bounds(function, x, domain):
    from sympy import limit
    maxi = domain.max()
    if maxi.is_infinite:
        maxi = limit(function, x, maxi)
    else:
        is_infinitesimal = maxi.is_infinitesimal
        if is_infinitesimal is True:
            maxi = limit(function, x, maxi.clear_infinitesimal(), '+')
        elif is_infinitesimal is False:
            maxi = limit(function, x, maxi.clear_infinitesimal(), '-')
        else:
            maxi = function.subs(x, maxi)

    mini = domain.min()
    if mini.is_infinite:
        mini = limit(function, x, mini)
    else:
        is_infinitesimal = mini.is_infinitesimal
        if is_infinitesimal is True:
            mini = limit(function, x, mini.clear_infinitesimal(), '+')
        elif is_infinitesimal is False:
            mini = limit(function, x, mini.clear_infinitesimal(), '-')
        else:
            mini = function.subs(x, mini)
    return maxi, mini


class Minimum(ExprWithLimits):
    r"""Represents unevaluated Minimum operator.
    """

    __slots__ = ['is_commutative']

    def __new__(cls, function, *symbols, **assumptions):
        obj = ExprWithLimits.__new__(cls, function, *symbols, **assumptions)
        return obj

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *ab = self.limits[0]

        if ab:
            domain = Interval(*ab)
        else:
            domain = x.domain

        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
    #             beta = p.coeff_monomial(S.One)
                if a.is_number:
                    if a > 0:
                        return self.function.subs(x, domain.min())
                    else:
                        return self.function.subs(x, domain.max())
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_number:
                    if a < 0:
                        return Min(*bounds(self.function, x, domain))
                    elif a > 0:
                        b = p.coeff_monomial(x)
                        zero_point = -b / (2 * a)
                        if zero_point in domain:
                            c = p.coeff_monomial(x)
                            return (4 * a * c - b * b) / (4 * a)
                        return Min(*bounds(self.function, x, domain))

            elif p.degree() <= 0:
                return self.function
        elif type(self.function) == Min:
            args = []
            for arg in self.function.args:
                args.append(self.func(arg, *self.limits).doit())
            return Min(*args)
        return self

    def eval_zeta_function(self, f, limits):
        """
        Check whether the function matches with the zeta function.
        If it matches, then return a `Piecewise` expression because
        zeta function does not converge unless `s > 1` and `q > 0`
        """
        i, a, b = limits
        w, y, z = Wild('w', exclude=[i]), Wild('y', exclude=[i]), Wild('z', exclude=[i])
        result = f.match((w * i + y) ** (-z))
        if result is not None and b == S.Infinity:
            coeff = 1 / result[w] ** result[z]
            s = result[z]
            q = result[y] / result[w] + a
            return Piecewise((coeff * zeta(s, q), And(q > 0, s > 1)), (self, True))

    def _eval_derivative(self, x):
        """
        Differentiate wrt x as long as x is not in the free symbols of any of
        the upper or lower limits.

        Sum(a*b*x, (x, 1, a)) can be differentiated wrt x or b but not `a`
        since the value of the sum is discontinuous in `a`. In a case
        involving a limit variable, the unevaluated derivative is returned.
        """

        # diff already confirmed that x is in the free symbols of self, but we
        # don't want to differentiate wrt any free symbol in the upper or lower
        # limits
        # XXX remove this test for free_symbols when the default _eval_derivative is in
        if isinstance(x, Symbol) and x not in self.free_symbols:
            return S.Zero

        # get limits and the function
        f, limits = self.function, list(self.limits)

        limit = limits.pop(-1)

        if limits:  # f is the argument to a Sum
            f = self.func(f, *limits)

        if len(limit) == 3:
            _, a, b = limit
            if x in a.free_symbols or x in b.free_symbols:
                return None
            df = Derivative(f, x, evaluate=True)
            rv = self.func(df, limit)
            return rv
        else:
            return NotImplementedError('Lower and upper bound expected.')

    def _eval_difference_delta(self, n, step):
        k, _, upper = self.args[-1]
        new_upper = upper.subs(n, n + step)

        if len(self.args) == 2:
            f = self.args[0]
        else:
            f = self.func(*self.args[:-1])

        return Sum(f, (k, upper + 1, new_upper)).doit()

    def _eval_simplify(self, ratio=1.7, measure=None, rational=False, inverse=False):
        from sympy.simplify.simplify import factor_sum, sum_combine
        from sympy.core.function import expand
        from sympy.core.mul import Mul

        # split the function into adds
        terms = Add.make_args(expand(self.function))
        s_t = []  # Sum Terms
        o_t = []  # Other Terms

        for term in terms:
            if term.has(Sum):
                # if there is an embedded sum here
                # it is of the form x * (Sum(whatever))
                # hence we make a Mul out of it, and simplify all interior sum terms
                subterms = Mul.make_args(expand(term))
                out_terms = []
                for subterm in subterms:
                    # go through each term
                    if isinstance(subterm, Sum):
                        # if it's a sum, simplify it
                        out_terms.append(subterm._eval_simplify())
                    else:
                        # otherwise, add it as is
                        out_terms.append(subterm)

                # turn it back into a Mul
                s_t.append(Mul(*out_terms))
            else:
                o_t.append(term)

        # next try to combine any interior sums for further simplification
        result = Add(sum_combine(s_t), *o_t)

        return factor_sum(result, limits=self.limits)

    def _eval_summation(self, f, x):
        return None

    def is_convergent(self):
        r"""Checks for the convergence of a Sum.

        We divide the study of convergence of infinite sums and products in
        two parts.

        First Part:
        One part is the question whether all the terms are well defined, i.e.,
        they are finite in a sum and also non-zero in a product. Zero
        is the analogy of (minus) infinity in products as
        :math:`e^{-\infty} = 0`.

        Second Part:
        The second part is the question of convergence after infinities,
        and zeros in products, have been omitted assuming that their number
        is finite. This means that we only consider the tail of the sum or
        product, starting from some point after which all terms are well
        defined.

        For example, in a sum of the form:

        .. math::

            \sum_{1 \leq i < \infty} \frac{1}{n^2 + an + b}

        where a and b are numbers. The routine will return true, even if there
        are infinities in the term sequence (at most two). An analogous
        product would be:

        .. math::

            \prod_{1 \leq i < \infty} e^{\frac{1}{n^2 + an + b}}

        This is how convergence is interpreted. It is concerned with what
        happens at the limit. Finding the bad terms is another independent
        matter.

        Note: It is responsibility of user to see that the sum or product
        is well defined.

        There are various tests employed to check the convergence like
        divergence test, root test, integral test, alternating series test,
        comparison tests, Dirichlet tests. It returns true if Sum is convergent
        and false if divergent and NotImplementedError if it can not be checked.

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Convergence_tests

        Examples
        ========

        >>> from sympy import factorial, S, Sum, Symbol, oo
        >>> n = Symbol('n', integer=True)
        >>> Sum(n/(n - 1), (n, 4, 7)).is_convergent()
        True
        >>> Sum(n/(2*n + 1), (n, 1, oo)).is_convergent()
        False
        >>> Sum(factorial(n)/5**n, (n, 1, oo)).is_convergent()
        False
        >>> Sum(1/n**(S(6)/5), (n, 1, oo)).is_convergent()
        True

        See Also
        ========

        Sum.is_absolutely_convergent()
        Product.is_convergent()
        """
        from sympy import Integral, log, symbols, simplify
        p, q, r = symbols('p q r', cls=Wild)

        sym = self.limits[0][0]
        lower_limit = self.limits[0][1]
        upper_limit = self.limits[0][2]
        sequence_term = self.function

        if len(sequence_term.free_symbols) > 1:
            raise NotImplementedError("convergence checking for more than one symbol "
                                      "containing series is not handled")

        if lower_limit.is_finite and upper_limit.is_finite:
            return S.true

        # transform sym -> -sym and swap the upper_limit = S.Infinity
        # and lower_limit = - upper_limit
        if lower_limit is S.NegativeInfinity:
            if upper_limit is S.Infinity:
                return Sum(sequence_term, (sym, 0, S.Infinity)).is_convergent() and \
                        Sum(sequence_term, (sym, S.NegativeInfinity, 0)).is_convergent()
            sequence_term = simplify(sequence_term.xreplace({sym:-sym}))
            lower_limit = -upper_limit
            upper_limit = S.Infinity

        sym_ = Dummy(sym.name, integer=True, positive=True)
        sequence_term = sequence_term.xreplace({sym: sym_})
        sym = sym_

        interval = Interval(lower_limit, upper_limit)

        # Piecewise function handle
        if sequence_term.is_Piecewise:
            for func, cond in sequence_term.args:
                # see if it represents something going to oo
                if cond == True or cond.as_set().sup is S.Infinity:
                    s = Sum(func, (sym, lower_limit, upper_limit))
                    return s.is_convergent()
            return S.true

        ###  -------- Divergence test ----------- ###
        try:
            lim_val = limit_seq(sequence_term, sym)
            if lim_val is not None and lim_val.is_zero is False:
                return S.false
        except NotImplementedError:
            pass

        try:
            lim_val_abs = limit_seq(abs(sequence_term), sym)
            if lim_val_abs is not None and lim_val_abs.is_zero is False:
                return S.false
        except NotImplementedError:
            pass

        order = O(sequence_term, (sym, S.Infinity))

        ### --------- p-series test (1/n**p) ---------- ###
        p1_series_test = order.expr.match(sym ** p)
        if p1_series_test is not None:
            if p1_series_test[p] < -1:
                return S.true
            if p1_series_test[p] >= -1:
                return S.false

        p2_series_test = order.expr.match((1 / sym) ** p)
        if p2_series_test is not None:
            if p2_series_test[p] > 1:
                return S.true
            if p2_series_test[p] <= 1:
                return S.false

        ### ------------- comparison test ------------- ###
        # 1/(n**p*log(n)**q*log(log(n))**r) comparison
        n_log_test = order.expr.match(1 / (sym ** p * log(sym) ** q * log(log(sym)) ** r))
        if n_log_test is not None:
            if (n_log_test[p] > 1 or
                (n_log_test[p] == 1 and n_log_test[q] > 1) or
                (n_log_test[p] == n_log_test[q] == 1 and n_log_test[r] > 1)):
                    return S.true
            return S.false

        ### ------------- Limit comparison test -----------###
        # (1/n) comparison
        try:
            lim_comp = limit_seq(sym * sequence_term, sym)
            if lim_comp is not None and lim_comp.is_number and lim_comp > 0:
                return S.false
        except NotImplementedError:
            pass

        ### ----------- ratio test ---------------- ###
        next_sequence_term = sequence_term.xreplace({sym: sym + 1})
        ratio = combsimp(powsimp(next_sequence_term / sequence_term))
        try:
            lim_ratio = limit_seq(ratio, sym)
            if lim_ratio is not None and lim_ratio.is_number:
                if abs(lim_ratio) > 1:
                    return S.false
                if abs(lim_ratio) < 1:
                    return S.true
        except NotImplementedError:
            pass

        ### ----------- root test ---------------- ###
        # lim = Limit(abs(sequence_term)**(1/sym), sym, S.Infinity)
        try:
            lim_evaluated = limit_seq(abs(sequence_term) ** (1 / sym), sym)
            if lim_evaluated is not None and lim_evaluated.is_number:
                if lim_evaluated < 1:
                    return S.true
                if lim_evaluated > 1:
                    return S.false
        except NotImplementedError:
            pass

        ### ------------- alternating series test ----------- ###
        dict_val = sequence_term.match((-1) ** (sym + p) * q)
        if not dict_val[p].has(sym) and is_decreasing(dict_val[q], interval):
            return S.true

        ### ------------- integral test -------------- ###
        check_interval = None
        maxima = solveset(sequence_term.diff(sym), sym, interval)
        if not maxima:
            check_interval = interval
        elif isinstance(maxima, FiniteSet) and maxima.sup.is_number:
            check_interval = Interval(maxima.sup, interval.sup)
        if (check_interval is not None and
            (is_decreasing(sequence_term, check_interval) or
            is_decreasing(-sequence_term, check_interval))):
                integral_val = Integral(
                    sequence_term, (sym, lower_limit, upper_limit))
                try:
                    integral_val_evaluated = integral_val.doit()
                    if integral_val_evaluated.is_number:
                        return S(integral_val_evaluated.is_finite)
                except NotImplementedError:
                    pass

        ### ----- Dirichlet and bounded times convergent tests ----- ###
        # TODO
        #
        # Dirichlet_test
        # https://en.wikipedia.org/wiki/Dirichlet%27s_test
        #
        # Bounded times convergent test
        # It is based on comparison theorems for series.
        # In particular, if the general term of a series can
        # be written as a product of two terms a_n and b_n
        # and if a_n is bounded and if Sum(b_n) is absolutely
        # convergent, then the original series Sum(a_n * b_n)
        # is absolutely convergent and so convergent.
        #
        # The following code can grows like 2**n where n is the
        # number of args in order.expr
        # Possibly combined with the potentially slow checks
        # inside the loop, could make this test extremely slow
        # for larger summation expressions.

        if order.expr.is_Mul:
            args = order.expr.args
            argset = set(args)

            ### -------------- Dirichlet tests -------------- ###
            m = Dummy('m', integer=True)

            def _dirichlet_test(g_n):
                try:
                    ing_val = limit_seq(Sum(g_n, (sym, interval.inf, m)).doit(), m)
                    if ing_val is not None and ing_val.is_finite:
                        return S.true
                except NotImplementedError:
                    pass

            ### -------- bounded times convergent test ---------###
            def _bounded_convergent_test(g1_n, g2_n):
                try:
                    lim_val = limit_seq(g1_n, sym)
                    if lim_val is not None and (lim_val.is_finite or (
                        isinstance(lim_val, AccumulationBounds)
                        and (lim_val.max - lim_val.min).is_finite)):
                            if Sum(g2_n, (sym, lower_limit, upper_limit)).is_absolutely_convergent():
                                return S.true
                except NotImplementedError:
                    pass

            for n in range(1, len(argset)):
                for a_tuple in itertools.combinations(args, n):
                    b_set = argset - set(a_tuple)
                    a_n = Mul(*a_tuple)
                    b_n = Mul(*b_set)

                    if is_decreasing(a_n, interval):
                        dirich = _dirichlet_test(b_n)
                        if dirich is not None:
                            return dirich

                    bc_test = _bounded_convergent_test(a_n, b_n)
                    if bc_test is not None:
                        return bc_test

        _sym = self.limits[0][0]
        sequence_term = sequence_term.xreplace({sym: _sym})
        raise NotImplementedError("The algorithm to find the Sum convergence of %s "
                                  "is not yet implemented" % (sequence_term))

    def is_absolutely_convergent(self):
        """
        Checks for the absolute convergence of an infinite series.

        Same as checking convergence of absolute value of sequence_term of
        an infinite series.

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Absolute_convergence

        Examples
        ========

        >>> from sympy import Sum, Symbol, sin, oo
        >>> n = Symbol('n', integer=True)
        >>> Sum((-1)**n, (n, 1, oo)).is_absolutely_convergent()
        False
        >>> Sum((-1)**n/n**2, (n, 1, oo)).is_absolutely_convergent()
        True

        See Also
        ========

        Sum.is_convergent()
        """
        return Sum(abs(self.function), self.limits).is_convergent()

    def euler_maclaurin(self, m=0, n=0, eps=0, eval_integral=True):
        """
        Return an Euler-Maclaurin approximation of self, where m is the
        number of leading terms to sum directly and n is the number of
        terms in the tail.

        With m = n = 0, this is simply the corresponding integral
        plus a first-order endpoint correction.

        Returns (s, e) where s is the Euler-Maclaurin approximation
        and e is the estimated error (taken to be the magnitude of
        the first omitted term in the tail):

            >>> from sympy.abc import k, a, b
            >>> from sympy import Sum
            >>> Sum(1/k, (k, 2, 5)).doit().evalf()
            1.28333333333333
            >>> s, e = Sum(1/k, (k, 2, 5)).euler_maclaurin()
            >>> s
            -log(2) + 7/20 + log(5)
            >>> from sympy import sstr
            >>> print(sstr((s.evalf(), e.evalf()), full_prec=True))
            (1.26629073187415, 0.0175000000000000)

        The endpoints may be symbolic:

            >>> s, e = Sum(1/k, (k, a, b)).euler_maclaurin()
            >>> s
            -log(a) + log(b) + 1/(2*b) + 1/(2*a)
            >>> e
            Abs(1/(12*b**2) - 1/(12*a**2))

        If the function is a polynomial of degree at most 2n+1, the
        Euler-Maclaurin formula becomes exact (and e = 0 is returned):

            >>> Sum(k, (k, 2, b)).euler_maclaurin()
            (b**2/2 + b/2 - 1, 0)
            >>> Sum(k, (k, 2, b)).doit()
            b**2/2 + b/2 - 1

        With a nonzero eps specified, the summation is ended
        as soon as the remainder term is less than the epsilon.
        """
        from sympy.functions import bernoulli, factorial
        from sympy.integrals import Integral

        m = int(m)
        n = int(n)
        f = self.function
        if len(self.limits) != 1:
            raise ValueError("More than 1 limit")
        i, a, b = self.limits[0]
        if (a > b) == True:
            if a - b == 1:
                return S.Zero, S.Zero
            a, b = b + 1, a - 1
            f = -f
        s = S.Zero
        if m:
            if b.is_Integer and a.is_Integer:
                m = min(m, b - a + 1)
            if not eps or f.is_polynomial(i):
                for k in range(m):
                    s += f.subs(i, a + k)
            else:
                term = f.subs(i, a)
                if term:
                    test = abs(term.evalf(3)) < eps
                    if test == True:
                        return s, abs(term)
                    elif not (test == False):
                        # a symbolic Relational class, can't go further
                        return term, S.Zero
                s += term
                for k in range(1, m):
                    term = f.subs(i, a + k)
                    if abs(term.evalf(3)) < eps and term != 0:
                        return s, abs(term)
                    s += term
            if b - a + 1 == m:
                return s, S.Zero
            a += m
        x = Dummy('x')
        I = Integral(f.subs(i, x), (x, a, b))
        if eval_integral:
            I = I.doit()
        s += I

        def fpoint(expr):
            if b is S.Infinity:
                return expr.subs(i, a), 0
            return expr.subs(i, a), expr.subs(i, b)

        fa, fb = fpoint(f)
        iterm = (fa + fb) / 2
        g = f.diff(i)
        for k in range(1, n + 2):
            ga, gb = fpoint(g)
            term = bernoulli(2 * k) / factorial(2 * k) * (gb - ga)
            if (eps and term and abs(term.evalf(3)) < eps) or (k > n):
                break
            s += term
            g = g.diff(i, 2, simplify=False)
        return s + iterm, abs(term)

    def reverse_order(self, *indices):
        """
        Reverse the order of a limit in a Sum.

        Usage
        =====

        ``reverse_order(self, *indices)`` reverses some limits in the expression
        ``self`` which can be either a ``Sum`` or a ``Product``. The selectors in
        the argument ``indices`` specify some indices whose limits get reversed.
        These selectors are either variable names or numerical indices counted
        starting from the inner-most limit tuple.

        Examples
        ========

        >>> from sympy import Sum
        >>> from sympy.abc import x, y, a, b, c, d

        >>> Sum(x, (x, 0, 3)).reverse_order(x)
        Sum(-x, (x, 4, -1))
        >>> Sum(x*y, (x, 1, 5), (y, 0, 6)).reverse_order(x, y)
        Sum(x*y, (x, 6, 0), (y, 7, -1))
        >>> Sum(x, (x, a, b)).reverse_order(x)
        Sum(-x, (x, b + 1, a - 1))
        >>> Sum(x, (x, a, b)).reverse_order(0)
        Sum(-x, (x, b + 1, a - 1))

        While one should prefer variable names when specifying which limits
        to reverse, the index counting notation comes in handy in case there
        are several symbols with the same name.

        >>> S = Sum(x**2, (x, a, b), (x, c, d))
        >>> S
        Sum(x**2, (x, a, b), (x, c, d))
        >>> S0 = S.reverse_order(0)
        >>> S0
        Sum(-x**2, (x, b + 1, a - 1), (x, c, d))
        >>> S1 = S0.reverse_order(1)
        >>> S1
        Sum(x**2, (x, b + 1, a - 1), (x, d + 1, c - 1))

        Of course we can mix both notations:

        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(x, 1)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))
        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(y, x)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))

        See Also
        ========

        index, reorder_limit, reorder

        References
        ==========

        .. [1] Michael Karr, "Summation in Finite Terms", Journal of the ACM,
               Volume 28 Issue 2, April 1981, Pages 305-350
               http://dl.acm.org/citation.cfm?doid=322248.322255
        """
        l_indices = list(indices)

        for i, indx in enumerate(l_indices):
            if not isinstance(indx, int):
                l_indices[i] = self.index(indx)

        e = 1
        limits = []
        for i, limit in enumerate(self.limits):
            l = limit
            if i in l_indices:
                e = -e
                l = (limit[0], limit[2] + 1, limit[1] - 1)
            limits.append(l)

        return Sum(e * self.function, *limits)

    def _print_Minimum(self, expr):
        l = [self._print(o) for o in expr.args]
        return "Min[%s](%s)" % ", ".join(l)

    def simplifier(self):
        (x, *_), *_ = self.limits
        independent, dependent = self.function.as_independent(x, as_Add=True)

        return self.func(dependent, *self.limits) + independent

    def as_Ref(self):
        return self.func(Ref(self.function, *self.limits).simplifier())

    def bisect(self, front=None, back=None):
        (x, *_), *_ = self.limits
        from sympy.tensor.indexed import Slice
        if isinstance(x, Slice):
            z, x = x.bisect(front, back)
            return self.func(self.func(self.function, (z,)).simplifier(), (x,))
        return self


class Maximum(ExprWithLimits):
    r"""Represents unevaluated Minimum operator.
    """

    __slots__ = ['is_commutative']

    def __new__(cls, function, *symbols, **assumptions):
        obj = ExprWithLimits.__new__(cls, function, *symbols, **assumptions)
        return obj

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *ab = self.limits[0]

        if ab:
            domain = Interval(*ab)
        else:
            domain = x.domain

        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_number:
                    if a > 0:
                        return self.function.subs(x, domain.max())
                    else:
                        return self.function.subs(x, domain.min())
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_number:
                    if a > 0:
                        return Max(*bounds(self.function, x, domain))
                    elif a > 0:
                        b = p.coeff_monomial(x)
                        zero_point = -b / (2 * a)
                        if zero_point in domain:
                            c = p.coeff_monomial(x)
                            return (4 * a * c - b * b) / (4 * a)
                        return Max(*bounds(self.function, x, domain))
                    else:
                        return self
            elif p.degree() <= 0:
                return self.function
        elif type(self.function) == Max:
            args = []
            for arg in self.function.args:
                args.append(self.func(arg, *self.limits).doit())
            return Max(*args)

        return self

    def eval_zeta_function(self, f, limits):
        """
        Check whether the function matches with the zeta function.
        If it matches, then return a `Piecewise` expression because
        zeta function does not converge unless `s > 1` and `q > 0`
        """
        i, a, b = limits
        w, y, z = Wild('w', exclude=[i]), Wild('y', exclude=[i]), Wild('z', exclude=[i])
        result = f.match((w * i + y) ** (-z))
        if result is not None and b == S.Infinity:
            coeff = 1 / result[w] ** result[z]
            s = result[z]
            q = result[y] / result[w] + a
            return Piecewise((coeff * zeta(s, q), And(q > 0, s > 1)), (self, True))

    def _eval_derivative(self, x):
        """
        Differentiate wrt x as long as x is not in the free symbols of any of
        the upper or lower limits.

        Sum(a*b*x, (x, 1, a)) can be differentiated wrt x or b but not `a`
        since the value of the sum is discontinuous in `a`. In a case
        involving a limit variable, the unevaluated derivative is returned.
        """

        # diff already confirmed that x is in the free symbols of self, but we
        # don't want to differentiate wrt any free symbol in the upper or lower
        # limits
        # XXX remove this test for free_symbols when the default _eval_derivative is in
        if isinstance(x, Symbol) and x not in self.free_symbols:
            return S.Zero

        # get limits and the function
        f, limits = self.function, list(self.limits)

        limit = limits.pop(-1)

        if limits:  # f is the argument to a Sum
            f = self.func(f, *limits)

        if len(limit) == 3:
            _, a, b = limit
            if x in a.free_symbols or x in b.free_symbols:
                return None
            df = Derivative(f, x, evaluate=True)
            rv = self.func(df, limit)
            return rv
        else:
            return NotImplementedError('Lower and upper bound expected.')

    def _eval_difference_delta(self, n, step):
        k, _, upper = self.args[-1]
        new_upper = upper.subs(n, n + step)

        if len(self.args) == 2:
            f = self.args[0]
        else:
            f = self.func(*self.args[:-1])

        return Sum(f, (k, upper + 1, new_upper)).doit()

    def _eval_simplify(self, ratio=1.7, measure=None, rational=False, inverse=False):
        from sympy.simplify.simplify import factor_sum, sum_combine
        from sympy.core.function import expand
        from sympy.core.mul import Mul

        # split the function into adds
        terms = Add.make_args(expand(self.function))
        s_t = []  # Sum Terms
        o_t = []  # Other Terms

        for term in terms:
            if term.has(Sum):
                # if there is an embedded sum here
                # it is of the form x * (Sum(whatever))
                # hence we make a Mul out of it, and simplify all interior sum terms
                subterms = Mul.make_args(expand(term))
                out_terms = []
                for subterm in subterms:
                    # go through each term
                    if isinstance(subterm, Sum):
                        # if it's a sum, simplify it
                        out_terms.append(subterm._eval_simplify())
                    else:
                        # otherwise, add it as is
                        out_terms.append(subterm)

                # turn it back into a Mul
                s_t.append(Mul(*out_terms))
            else:
                o_t.append(term)

        # next try to combine any interior sums for further simplification
        result = Add(sum_combine(s_t), *o_t)

        return factor_sum(result, limits=self.limits)

    def _eval_summation(self, f, x):
        return None

    def is_convergent(self):
        r"""Checks for the convergence of a Sum.

        We divide the study of convergence of infinite sums and products in
        two parts.

        First Part:
        One part is the question whether all the terms are well defined, i.e.,
        they are finite in a sum and also non-zero in a product. Zero
        is the analogy of (minus) infinity in products as
        :math:`e^{-\infty} = 0`.

        Second Part:
        The second part is the question of convergence after infinities,
        and zeros in products, have been omitted assuming that their number
        is finite. This means that we only consider the tail of the sum or
        product, starting from some point after which all terms are well
        defined.

        For example, in a sum of the form:

        .. math::

            \sum_{1 \leq i < \infty} \frac{1}{n^2 + an + b}

        where a and b are numbers. The routine will return true, even if there
        are infinities in the term sequence (at most two). An analogous
        product would be:

        .. math::

            \prod_{1 \leq i < \infty} e^{\frac{1}{n^2 + an + b}}

        This is how convergence is interpreted. It is concerned with what
        happens at the limit. Finding the bad terms is another independent
        matter.

        Note: It is responsibility of user to see that the sum or product
        is well defined.

        There are various tests employed to check the convergence like
        divergence test, root test, integral test, alternating series test,
        comparison tests, Dirichlet tests. It returns true if Sum is convergent
        and false if divergent and NotImplementedError if it can not be checked.

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Convergence_tests

        Examples
        ========

        >>> from sympy import factorial, S, Sum, Symbol, oo
        >>> n = Symbol('n', integer=True)
        >>> Sum(n/(n - 1), (n, 4, 7)).is_convergent()
        True
        >>> Sum(n/(2*n + 1), (n, 1, oo)).is_convergent()
        False
        >>> Sum(factorial(n)/5**n, (n, 1, oo)).is_convergent()
        False
        >>> Sum(1/n**(S(6)/5), (n, 1, oo)).is_convergent()
        True

        See Also
        ========

        Sum.is_absolutely_convergent()
        Product.is_convergent()
        """
        from sympy import Integral, log, symbols, simplify
        p, q, r = symbols('p q r', cls=Wild)

        sym = self.limits[0][0]
        lower_limit = self.limits[0][1]
        upper_limit = self.limits[0][2]
        sequence_term = self.function

        if len(sequence_term.free_symbols) > 1:
            raise NotImplementedError("convergence checking for more than one symbol "
                                      "containing series is not handled")

        if lower_limit.is_finite and upper_limit.is_finite:
            return S.true

        # transform sym -> -sym and swap the upper_limit = S.Infinity
        # and lower_limit = - upper_limit
        if lower_limit is S.NegativeInfinity:
            if upper_limit is S.Infinity:
                return Sum(sequence_term, (sym, 0, S.Infinity)).is_convergent() and \
                        Sum(sequence_term, (sym, S.NegativeInfinity, 0)).is_convergent()
            sequence_term = simplify(sequence_term.xreplace({sym:-sym}))
            lower_limit = -upper_limit
            upper_limit = S.Infinity

        sym_ = Dummy(sym.name, integer=True, positive=True)
        sequence_term = sequence_term.xreplace({sym: sym_})
        sym = sym_

        interval = Interval(lower_limit, upper_limit)

        # Piecewise function handle
        if sequence_term.is_Piecewise:
            for func, cond in sequence_term.args:
                # see if it represents something going to oo
                if cond == True or cond.as_set().sup is S.Infinity:
                    s = Sum(func, (sym, lower_limit, upper_limit))
                    return s.is_convergent()
            return S.true

        ###  -------- Divergence test ----------- ###
        try:
            lim_val = limit_seq(sequence_term, sym)
            if lim_val is not None and lim_val.is_zero is False:
                return S.false
        except NotImplementedError:
            pass

        try:
            lim_val_abs = limit_seq(abs(sequence_term), sym)
            if lim_val_abs is not None and lim_val_abs.is_zero is False:
                return S.false
        except NotImplementedError:
            pass

        order = O(sequence_term, (sym, S.Infinity))

        ### --------- p-series test (1/n**p) ---------- ###
        p1_series_test = order.expr.match(sym ** p)
        if p1_series_test is not None:
            if p1_series_test[p] < -1:
                return S.true
            if p1_series_test[p] >= -1:
                return S.false

        p2_series_test = order.expr.match((1 / sym) ** p)
        if p2_series_test is not None:
            if p2_series_test[p] > 1:
                return S.true
            if p2_series_test[p] <= 1:
                return S.false

        ### ------------- comparison test ------------- ###
        # 1/(n**p*log(n)**q*log(log(n))**r) comparison
        n_log_test = order.expr.match(1 / (sym ** p * log(sym) ** q * log(log(sym)) ** r))
        if n_log_test is not None:
            if (n_log_test[p] > 1 or
                (n_log_test[p] == 1 and n_log_test[q] > 1) or
                (n_log_test[p] == n_log_test[q] == 1 and n_log_test[r] > 1)):
                    return S.true
            return S.false

        ### ------------- Limit comparison test -----------###
        # (1/n) comparison
        try:
            lim_comp = limit_seq(sym * sequence_term, sym)
            if lim_comp is not None and lim_comp.is_number and lim_comp > 0:
                return S.false
        except NotImplementedError:
            pass

        ### ----------- ratio test ---------------- ###
        next_sequence_term = sequence_term.xreplace({sym: sym + 1})
        ratio = combsimp(powsimp(next_sequence_term / sequence_term))
        try:
            lim_ratio = limit_seq(ratio, sym)
            if lim_ratio is not None and lim_ratio.is_number:
                if abs(lim_ratio) > 1:
                    return S.false
                if abs(lim_ratio) < 1:
                    return S.true
        except NotImplementedError:
            pass

        ### ----------- root test ---------------- ###
        # lim = Limit(abs(sequence_term)**(1/sym), sym, S.Infinity)
        try:
            lim_evaluated = limit_seq(abs(sequence_term) ** (1 / sym), sym)
            if lim_evaluated is not None and lim_evaluated.is_number:
                if lim_evaluated < 1:
                    return S.true
                if lim_evaluated > 1:
                    return S.false
        except NotImplementedError:
            pass

        ### ------------- alternating series test ----------- ###
        dict_val = sequence_term.match((-1) ** (sym + p) * q)
        if not dict_val[p].has(sym) and is_decreasing(dict_val[q], interval):
            return S.true

        ### ------------- integral test -------------- ###
        check_interval = None
        maxima = solveset(sequence_term.diff(sym), sym, interval)
        if not maxima:
            check_interval = interval
        elif isinstance(maxima, FiniteSet) and maxima.sup.is_number:
            check_interval = Interval(maxima.sup, interval.sup)
        if (check_interval is not None and
            (is_decreasing(sequence_term, check_interval) or
            is_decreasing(-sequence_term, check_interval))):
                integral_val = Integral(
                    sequence_term, (sym, lower_limit, upper_limit))
                try:
                    integral_val_evaluated = integral_val.doit()
                    if integral_val_evaluated.is_number:
                        return S(integral_val_evaluated.is_finite)
                except NotImplementedError:
                    pass

        ### ----- Dirichlet and bounded times convergent tests ----- ###
        # TODO
        #
        # Dirichlet_test
        # https://en.wikipedia.org/wiki/Dirichlet%27s_test
        #
        # Bounded times convergent test
        # It is based on comparison theorems for series.
        # In particular, if the general term of a series can
        # be written as a product of two terms a_n and b_n
        # and if a_n is bounded and if Sum(b_n) is absolutely
        # convergent, then the original series Sum(a_n * b_n)
        # is absolutely convergent and so convergent.
        #
        # The following code can grows like 2**n where n is the
        # number of args in order.expr
        # Possibly combined with the potentially slow checks
        # inside the loop, could make this test extremely slow
        # for larger summation expressions.

        if order.expr.is_Mul:
            args = order.expr.args
            argset = set(args)

            ### -------------- Dirichlet tests -------------- ###
            m = Dummy('m', integer=True)

            def _dirichlet_test(g_n):
                try:
                    ing_val = limit_seq(Sum(g_n, (sym, interval.inf, m)).doit(), m)
                    if ing_val is not None and ing_val.is_finite:
                        return S.true
                except NotImplementedError:
                    pass

            ### -------- bounded times convergent test ---------###
            def _bounded_convergent_test(g1_n, g2_n):
                try:
                    lim_val = limit_seq(g1_n, sym)
                    if lim_val is not None and (lim_val.is_finite or (
                        isinstance(lim_val, AccumulationBounds)
                        and (lim_val.max - lim_val.min).is_finite)):
                            if Sum(g2_n, (sym, lower_limit, upper_limit)).is_absolutely_convergent():
                                return S.true
                except NotImplementedError:
                    pass

            for n in range(1, len(argset)):
                for a_tuple in itertools.combinations(args, n):
                    b_set = argset - set(a_tuple)
                    a_n = Mul(*a_tuple)
                    b_n = Mul(*b_set)

                    if is_decreasing(a_n, interval):
                        dirich = _dirichlet_test(b_n)
                        if dirich is not None:
                            return dirich

                    bc_test = _bounded_convergent_test(a_n, b_n)
                    if bc_test is not None:
                        return bc_test

        _sym = self.limits[0][0]
        sequence_term = sequence_term.xreplace({sym: _sym})
        raise NotImplementedError("The algorithm to find the Sum convergence of %s "
                                  "is not yet implemented" % (sequence_term))

    def is_absolutely_convergent(self):
        """
        Checks for the absolute convergence of an infinite series.

        Same as checking convergence of absolute value of sequence_term of
        an infinite series.

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Absolute_convergence

        Examples
        ========

        >>> from sympy import Sum, Symbol, sin, oo
        >>> n = Symbol('n', integer=True)
        >>> Sum((-1)**n, (n, 1, oo)).is_absolutely_convergent()
        False
        >>> Sum((-1)**n/n**2, (n, 1, oo)).is_absolutely_convergent()
        True

        See Also
        ========

        Sum.is_convergent()
        """
        return Sum(abs(self.function), self.limits).is_convergent()

    def euler_maclaurin(self, m=0, n=0, eps=0, eval_integral=True):
        """
        Return an Euler-Maclaurin approximation of self, where m is the
        number of leading terms to sum directly and n is the number of
        terms in the tail.

        With m = n = 0, this is simply the corresponding integral
        plus a first-order endpoint correction.

        Returns (s, e) where s is the Euler-Maclaurin approximation
        and e is the estimated error (taken to be the magnitude of
        the first omitted term in the tail):

            >>> from sympy.abc import k, a, b
            >>> from sympy import Sum
            >>> Sum(1/k, (k, 2, 5)).doit().evalf()
            1.28333333333333
            >>> s, e = Sum(1/k, (k, 2, 5)).euler_maclaurin()
            >>> s
            -log(2) + 7/20 + log(5)
            >>> from sympy import sstr
            >>> print(sstr((s.evalf(), e.evalf()), full_prec=True))
            (1.26629073187415, 0.0175000000000000)

        The endpoints may be symbolic:

            >>> s, e = Sum(1/k, (k, a, b)).euler_maclaurin()
            >>> s
            -log(a) + log(b) + 1/(2*b) + 1/(2*a)
            >>> e
            Abs(1/(12*b**2) - 1/(12*a**2))

        If the function is a polynomial of degree at most 2n+1, the
        Euler-Maclaurin formula becomes exact (and e = 0 is returned):

            >>> Sum(k, (k, 2, b)).euler_maclaurin()
            (b**2/2 + b/2 - 1, 0)
            >>> Sum(k, (k, 2, b)).doit()
            b**2/2 + b/2 - 1

        With a nonzero eps specified, the summation is ended
        as soon as the remainder term is less than the epsilon.
        """
        from sympy.functions import bernoulli, factorial
        from sympy.integrals import Integral

        m = int(m)
        n = int(n)
        f = self.function
        if len(self.limits) != 1:
            raise ValueError("More than 1 limit")
        i, a, b = self.limits[0]
        if (a > b) == True:
            if a - b == 1:
                return S.Zero, S.Zero
            a, b = b + 1, a - 1
            f = -f
        s = S.Zero
        if m:
            if b.is_Integer and a.is_Integer:
                m = min(m, b - a + 1)
            if not eps or f.is_polynomial(i):
                for k in range(m):
                    s += f.subs(i, a + k)
            else:
                term = f.subs(i, a)
                if term:
                    test = abs(term.evalf(3)) < eps
                    if test == True:
                        return s, abs(term)
                    elif not (test == False):
                        # a symbolic Relational class, can't go further
                        return term, S.Zero
                s += term
                for k in range(1, m):
                    term = f.subs(i, a + k)
                    if abs(term.evalf(3)) < eps and term != 0:
                        return s, abs(term)
                    s += term
            if b - a + 1 == m:
                return s, S.Zero
            a += m
        x = Dummy('x')
        I = Integral(f.subs(i, x), (x, a, b))
        if eval_integral:
            I = I.doit()
        s += I

        def fpoint(expr):
            if b is S.Infinity:
                return expr.subs(i, a), 0
            return expr.subs(i, a), expr.subs(i, b)

        fa, fb = fpoint(f)
        iterm = (fa + fb) / 2
        g = f.diff(i)
        for k in range(1, n + 2):
            ga, gb = fpoint(g)
            term = bernoulli(2 * k) / factorial(2 * k) * (gb - ga)
            if (eps and term and abs(term.evalf(3)) < eps) or (k > n):
                break
            s += term
            g = g.diff(i, 2, simplify=False)
        return s + iterm, abs(term)

    def reverse_order(self, *indices):
        """
        Reverse the order of a limit in a Sum.

        Usage
        =====

        ``reverse_order(self, *indices)`` reverses some limits in the expression
        ``self`` which can be either a ``Sum`` or a ``Product``. The selectors in
        the argument ``indices`` specify some indices whose limits get reversed.
        These selectors are either variable names or numerical indices counted
        starting from the inner-most limit tuple.

        Examples
        ========

        >>> from sympy import Sum
        >>> from sympy.abc import x, y, a, b, c, d

        >>> Sum(x, (x, 0, 3)).reverse_order(x)
        Sum(-x, (x, 4, -1))
        >>> Sum(x*y, (x, 1, 5), (y, 0, 6)).reverse_order(x, y)
        Sum(x*y, (x, 6, 0), (y, 7, -1))
        >>> Sum(x, (x, a, b)).reverse_order(x)
        Sum(-x, (x, b + 1, a - 1))
        >>> Sum(x, (x, a, b)).reverse_order(0)
        Sum(-x, (x, b + 1, a - 1))

        While one should prefer variable names when specifying which limits
        to reverse, the index counting notation comes in handy in case there
        are several symbols with the same name.

        >>> S = Sum(x**2, (x, a, b), (x, c, d))
        >>> S
        Sum(x**2, (x, a, b), (x, c, d))
        >>> S0 = S.reverse_order(0)
        >>> S0
        Sum(-x**2, (x, b + 1, a - 1), (x, c, d))
        >>> S1 = S0.reverse_order(1)
        >>> S1
        Sum(x**2, (x, b + 1, a - 1), (x, d + 1, c - 1))

        Of course we can mix both notations:

        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(x, 1)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))
        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(y, x)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))

        See Also
        ========

        index, reorder_limit, reorder

        References
        ==========

        .. [1] Michael Karr, "Summation in Finite Terms", Journal of the ACM,
               Volume 28 Issue 2, April 1981, Pages 305-350
               http://dl.acm.org/citation.cfm?doid=322248.322255
        """
        l_indices = list(indices)

        for i, indx in enumerate(l_indices):
            if not isinstance(indx, int):
                l_indices[i] = self.index(indx)

        e = 1
        limits = []
        for i, limit in enumerate(self.limits):
            l = limit
            if i in l_indices:
                e = -e
                l = (limit[0], limit[2] + 1, limit[1] - 1)
            limits.append(l)

        return Sum(e * self.function, *limits)

    def _print_Maximum(self, expr):
        l = [self._print(o) for o in expr.args]
        return "Max[%s](%s)" % ", ".join(l)

    def simplifier(self):
        (x, *_), *_ = self.limits
        independent, dependent = self.function.as_independent(x, as_Add=True)

        return self.func(dependent, *self.limits) + independent

    def as_Ref(self):
        return self.func(Ref(self.function, *self.limits).simplifier())

    def separate(self):
        (x, *_), *_ = self.limits
        from sympy.tensor.indexed import Slice
        if isinstance(x, Slice):
            z, x = x.pop()
            return self.func(self.func(self.function, (x,)).simplifier(), (z,))
        return self


class Ref(ExprWithLimits):
    r"""Represents unevaluated reference operator.
    """

    __slots__ = ['is_commutative']

    def __new__(cls, function, *symbols, **assumptions):
        if isinstance(function, Relational):
            lhs = ExprWithLimits.__new__(cls, function.lhs, *symbols, **assumptions).simplifier()
            rhs = ExprWithLimits.__new__(cls, function.rhs, *symbols, **assumptions).simplifier()
            return function.func(lhs, rhs)

        from sympy.core.symbol import Symbol

        symbols = list(symbols)

        for i, limit in enumerate(symbols):
            if isinstance(limit, tuple) and len(limit) > 1:
                x, n = limit
                if 'domain' in x._assumptions:
#                     local variable
                    _x = Symbol(x.name, integer=True)
                    symbols[i] = (Symbol(x.name, integer=True), n)

                    function = function.subs(x, _x)

        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        return self

    def as_coeff_mmul(self):
        return 1, self

    def eval_zeta_function(self, f, limits):
        """
        Check whether the function matches with the zeta function.
        If it matches, then return a `Piecewise` expression because
        zeta function does not converge unless `s > 1` and `q > 0`
        """
        i, a, b = limits
        w, y, z = Wild('w', exclude=[i]), Wild('y', exclude=[i]), Wild('z', exclude=[i])
        result = f.match((w * i + y) ** (-z))
        if result is not None and b == S.Infinity:
            coeff = 1 / result[w] ** result[z]
            s = result[z]
            q = result[y] / result[w] + a
            return Piecewise((coeff * zeta(s, q), And(q > 0, s > 1)), (self, True))

    def _eval_derivative(self, x):
        """
        Differentiate wrt x as long as x is not in the free symbols of any of
        the upper or lower limits.

        Sum(a*b*x, (x, 1, a)) can be differentiated wrt x or b but not `a`
        since the value of the sum is discontinuous in `a`. In a case
        involving a limit variable, the unevaluated derivative is returned.
        """

        # diff already confirmed that x is in the free symbols of self, but we
        # don't want to differentiate wrt any free symbol in the upper or lower
        # limits
        # XXX remove this test for free_symbols when the default _eval_derivative is in
        if isinstance(x, Symbol) and x not in self.free_symbols:
            return S.Zero

        # get limits and the function
        f, limits = self.function, list(self.limits)

        limit = limits.pop(-1)

        if limits:  # f is the argument to a Sum
            f = self.func(f, *limits)

        if len(limit) == 3:
            _, a, b = limit
            if x in a.free_symbols or x in b.free_symbols:
                return None
            df = Derivative(f, x, evaluate=True)
            rv = self.func(df, limit)
            return rv
        else:
            return NotImplementedError('Lower and upper bound expected.')

    def _eval_difference_delta(self, n, step):
        k, _, upper = self.args[-1]
        new_upper = upper.subs(n, n + step)

        if len(self.args) == 2:
            f = self.args[0]
        else:
            f = self.func(*self.args[:-1])

        return Sum(f, (k, upper + 1, new_upper)).doit()

    def _eval_simplify(self, ratio=1.7, measure=None, rational=False, inverse=False):
        from sympy.simplify.simplify import factor_sum, sum_combine
        from sympy.core.function import expand
        from sympy.core.mul import Mul

        # split the function into adds
        terms = Add.make_args(expand(self.function))
        s_t = []  # Sum Terms
        o_t = []  # Other Terms

        for term in terms:
            if term.has(Sum):
                # if there is an embedded sum here
                # it is of the form x * (Sum(whatever))
                # hence we make a Mul out of it, and simplify all interior sum terms
                subterms = Mul.make_args(expand(term))
                out_terms = []
                for subterm in subterms:
                    # go through each term
                    if isinstance(subterm, Sum):
                        # if it's a sum, simplify it
                        out_terms.append(subterm._eval_simplify())
                    else:
                        # otherwise, add it as is
                        out_terms.append(subterm)

                # turn it back into a Mul
                s_t.append(Mul(*out_terms))
            else:
                o_t.append(term)

        # next try to combine any interior sums for further simplification
        result = Add(sum_combine(s_t), *o_t)

        return factor_sum(result, limits=self.limits)

    def _eval_summation(self, f, x):
        return None

    def is_convergent(self):
        r"""Checks for the convergence of a Sum.

        We divide the study of convergence of infinite sums and products in
        two parts.

        First Part:
        One part is the question whether all the terms are well defined, i.e.,
        they are finite in a sum and also non-zero in a product. Zero
        is the analogy of (minus) infinity in products as
        :math:`e^{-\infty} = 0`.

        Second Part:
        The second part is the question of convergence after infinities,
        and zeros in products, have been omitted assuming that their number
        is finite. This means that we only consider the tail of the sum or
        product, starting from some point after which all terms are well
        defined.

        For example, in a sum of the form:

        .. math::

            \sum_{1 \leq i < \infty} \frac{1}{n^2 + an + b}

        where a and b are numbers. The routine will return true, even if there
        are infinities in the term sequence (at most two). An analogous
        product would be:

        .. math::

            \prod_{1 \leq i < \infty} e^{\frac{1}{n^2 + an + b}}

        This is how convergence is interpreted. It is concerned with what
        happens at the limit. Finding the bad terms is another independent
        matter.

        Note: It is responsibility of user to see that the sum or product
        is well defined.

        There are various tests employed to check the convergence like
        divergence test, root test, integral test, alternating series test,
        comparison tests, Dirichlet tests. It returns true if Sum is convergent
        and false if divergent and NotImplementedError if it can not be checked.

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Convergence_tests

        Examples
        ========

        >>> from sympy import factorial, S, Sum, Symbol, oo
        >>> n = Symbol('n', integer=True)
        >>> Sum(n/(n - 1), (n, 4, 7)).is_convergent()
        True
        >>> Sum(n/(2*n + 1), (n, 1, oo)).is_convergent()
        False
        >>> Sum(factorial(n)/5**n, (n, 1, oo)).is_convergent()
        False
        >>> Sum(1/n**(S(6)/5), (n, 1, oo)).is_convergent()
        True

        See Also
        ========

        Sum.is_absolutely_convergent()
        Product.is_convergent()
        """
        from sympy import Integral, log, symbols, simplify
        p, q, r = symbols('p q r', cls=Wild)

        sym = self.limits[0][0]
        lower_limit = self.limits[0][1]
        upper_limit = self.limits[0][2]
        sequence_term = self.function

        if len(sequence_term.free_symbols) > 1:
            raise NotImplementedError("convergence checking for more than one symbol "
                                      "containing series is not handled")

        if lower_limit.is_finite and upper_limit.is_finite:
            return S.true

        # transform sym -> -sym and swap the upper_limit = S.Infinity
        # and lower_limit = - upper_limit
        if lower_limit is S.NegativeInfinity:
            if upper_limit is S.Infinity:
                return Sum(sequence_term, (sym, 0, S.Infinity)).is_convergent() and \
                        Sum(sequence_term, (sym, S.NegativeInfinity, 0)).is_convergent()
            sequence_term = simplify(sequence_term.xreplace({sym:-sym}))
            lower_limit = -upper_limit
            upper_limit = S.Infinity

        sym_ = Dummy(sym.name, integer=True, positive=True)
        sequence_term = sequence_term.xreplace({sym: sym_})
        sym = sym_

        interval = Interval(lower_limit, upper_limit)

        # Piecewise function handle
        if sequence_term.is_Piecewise:
            for func, cond in sequence_term.args:
                # see if it represents something going to oo
                if cond == True or cond.as_set().sup is S.Infinity:
                    s = Sum(func, (sym, lower_limit, upper_limit))
                    return s.is_convergent()
            return S.true

        ###  -------- Divergence test ----------- ###
        try:
            lim_val = limit_seq(sequence_term, sym)
            if lim_val is not None and lim_val.is_zero is False:
                return S.false
        except NotImplementedError:
            pass

        try:
            lim_val_abs = limit_seq(abs(sequence_term), sym)
            if lim_val_abs is not None and lim_val_abs.is_zero is False:
                return S.false
        except NotImplementedError:
            pass

        order = O(sequence_term, (sym, S.Infinity))

        ### --------- p-series test (1/n**p) ---------- ###
        p1_series_test = order.expr.match(sym ** p)
        if p1_series_test is not None:
            if p1_series_test[p] < -1:
                return S.true
            if p1_series_test[p] >= -1:
                return S.false

        p2_series_test = order.expr.match((1 / sym) ** p)
        if p2_series_test is not None:
            if p2_series_test[p] > 1:
                return S.true
            if p2_series_test[p] <= 1:
                return S.false

        ### ------------- comparison test ------------- ###
        # 1/(n**p*log(n)**q*log(log(n))**r) comparison
        n_log_test = order.expr.match(1 / (sym ** p * log(sym) ** q * log(log(sym)) ** r))
        if n_log_test is not None:
            if (n_log_test[p] > 1 or
                (n_log_test[p] == 1 and n_log_test[q] > 1) or
                (n_log_test[p] == n_log_test[q] == 1 and n_log_test[r] > 1)):
                    return S.true
            return S.false

        ### ------------- Limit comparison test -----------###
        # (1/n) comparison
        try:
            lim_comp = limit_seq(sym * sequence_term, sym)
            if lim_comp is not None and lim_comp.is_number and lim_comp > 0:
                return S.false
        except NotImplementedError:
            pass

        ### ----------- ratio test ---------------- ###
        next_sequence_term = sequence_term.xreplace({sym: sym + 1})
        ratio = combsimp(powsimp(next_sequence_term / sequence_term))
        try:
            lim_ratio = limit_seq(ratio, sym)
            if lim_ratio is not None and lim_ratio.is_number:
                if abs(lim_ratio) > 1:
                    return S.false
                if abs(lim_ratio) < 1:
                    return S.true
        except NotImplementedError:
            pass

        ### ----------- root test ---------------- ###
        # lim = Limit(abs(sequence_term)**(1/sym), sym, S.Infinity)
        try:
            lim_evaluated = limit_seq(abs(sequence_term) ** (1 / sym), sym)
            if lim_evaluated is not None and lim_evaluated.is_number:
                if lim_evaluated < 1:
                    return S.true
                if lim_evaluated > 1:
                    return S.false
        except NotImplementedError:
            pass

        ### ------------- alternating series test ----------- ###
        dict_val = sequence_term.match((-1) ** (sym + p) * q)
        if not dict_val[p].has(sym) and is_decreasing(dict_val[q], interval):
            return S.true

        ### ------------- integral test -------------- ###
        check_interval = None
        maxima = solveset(sequence_term.diff(sym), sym, interval)
        if not maxima:
            check_interval = interval
        elif isinstance(maxima, FiniteSet) and maxima.sup.is_number:
            check_interval = Interval(maxima.sup, interval.sup)
        if (check_interval is not None and
            (is_decreasing(sequence_term, check_interval) or
            is_decreasing(-sequence_term, check_interval))):
                integral_val = Integral(
                    sequence_term, (sym, lower_limit, upper_limit))
                try:
                    integral_val_evaluated = integral_val.doit()
                    if integral_val_evaluated.is_number:
                        return S(integral_val_evaluated.is_finite)
                except NotImplementedError:
                    pass

        ### ----- Dirichlet and bounded times convergent tests ----- ###
        # TODO
        #
        # Dirichlet_test
        # https://en.wikipedia.org/wiki/Dirichlet%27s_test
        #
        # Bounded times convergent test
        # It is based on comparison theorems for series.
        # In particular, if the general term of a series can
        # be written as a product of two terms a_n and b_n
        # and if a_n is bounded and if Sum(b_n) is absolutely
        # convergent, then the original series Sum(a_n * b_n)
        # is absolutely convergent and so convergent.
        #
        # The following code can grows like 2**n where n is the
        # number of args in order.expr
        # Possibly combined with the potentially slow checks
        # inside the loop, could make this test extremely slow
        # for larger summation expressions.

        if order.expr.is_Mul:
            args = order.expr.args
            argset = set(args)

            ### -------------- Dirichlet tests -------------- ###
            m = Dummy('m', integer=True)

            def _dirichlet_test(g_n):
                try:
                    ing_val = limit_seq(Sum(g_n, (sym, interval.inf, m)).doit(), m)
                    if ing_val is not None and ing_val.is_finite:
                        return S.true
                except NotImplementedError:
                    pass

            ### -------- bounded times convergent test ---------###
            def _bounded_convergent_test(g1_n, g2_n):
                try:
                    lim_val = limit_seq(g1_n, sym)
                    if lim_val is not None and (lim_val.is_finite or (
                        isinstance(lim_val, AccumulationBounds)
                        and (lim_val.max - lim_val.min).is_finite)):
                            if Sum(g2_n, (sym, lower_limit, upper_limit)).is_absolutely_convergent():
                                return S.true
                except NotImplementedError:
                    pass

            for n in range(1, len(argset)):
                for a_tuple in itertools.combinations(args, n):
                    b_set = argset - set(a_tuple)
                    a_n = Mul(*a_tuple)
                    b_n = Mul(*b_set)

                    if is_decreasing(a_n, interval):
                        dirich = _dirichlet_test(b_n)
                        if dirich is not None:
                            return dirich

                    bc_test = _bounded_convergent_test(a_n, b_n)
                    if bc_test is not None:
                        return bc_test

        _sym = self.limits[0][0]
        sequence_term = sequence_term.xreplace({sym: _sym})
        raise NotImplementedError("The algorithm to find the Sum convergence of %s "
                                  "is not yet implemented" % (sequence_term))

    def is_absolutely_convergent(self):
        """
        Checks for the absolute convergence of an infinite series.

        Same as checking convergence of absolute value of sequence_term of
        an infinite series.

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Absolute_convergence

        Examples
        ========

        >>> from sympy import Sum, Symbol, sin, oo
        >>> n = Symbol('n', integer=True)
        >>> Sum((-1)**n, (n, 1, oo)).is_absolutely_convergent()
        False
        >>> Sum((-1)**n/n**2, (n, 1, oo)).is_absolutely_convergent()
        True

        See Also
        ========

        Sum.is_convergent()
        """
        return Sum(abs(self.function), self.limits).is_convergent()

    def euler_maclaurin(self, m=0, n=0, eps=0, eval_integral=True):
        """
        Return an Euler-Maclaurin approximation of self, where m is the
        number of leading terms to sum directly and n is the number of
        terms in the tail.

        With m = n = 0, this is simply the corresponding integral
        plus a first-order endpoint correction.

        Returns (s, e) where s is the Euler-Maclaurin approximation
        and e is the estimated error (taken to be the magnitude of
        the first omitted term in the tail):

            >>> from sympy.abc import k, a, b
            >>> from sympy import Sum
            >>> Sum(1/k, (k, 2, 5)).doit().evalf()
            1.28333333333333
            >>> s, e = Sum(1/k, (k, 2, 5)).euler_maclaurin()
            >>> s
            -log(2) + 7/20 + log(5)
            >>> from sympy import sstr
            >>> print(sstr((s.evalf(), e.evalf()), full_prec=True))
            (1.26629073187415, 0.0175000000000000)

        The endpoints may be symbolic:

            >>> s, e = Sum(1/k, (k, a, b)).euler_maclaurin()
            >>> s
            -log(a) + log(b) + 1/(2*b) + 1/(2*a)
            >>> e
            Abs(1/(12*b**2) - 1/(12*a**2))

        If the function is a polynomial of degree at most 2n+1, the
        Euler-Maclaurin formula becomes exact (and e = 0 is returned):

            >>> Sum(k, (k, 2, b)).euler_maclaurin()
            (b**2/2 + b/2 - 1, 0)
            >>> Sum(k, (k, 2, b)).doit()
            b**2/2 + b/2 - 1

        With a nonzero eps specified, the summation is ended
        as soon as the remainder term is less than the epsilon.
        """
        from sympy.functions import bernoulli, factorial
        from sympy.integrals import Integral

        m = int(m)
        n = int(n)
        f = self.function
        if len(self.limits) != 1:
            raise ValueError("More than 1 limit")
        i, a, b = self.limits[0]
        if (a > b) == True:
            if a - b == 1:
                return S.Zero, S.Zero
            a, b = b + 1, a - 1
            f = -f
        s = S.Zero
        if m:
            if b.is_Integer and a.is_Integer:
                m = min(m, b - a + 1)
            if not eps or f.is_polynomial(i):
                for k in range(m):
                    s += f.subs(i, a + k)
            else:
                term = f.subs(i, a)
                if term:
                    test = abs(term.evalf(3)) < eps
                    if test == True:
                        return s, abs(term)
                    elif not (test == False):
                        # a symbolic Relational class, can't go further
                        return term, S.Zero
                s += term
                for k in range(1, m):
                    term = f.subs(i, a + k)
                    if abs(term.evalf(3)) < eps and term != 0:
                        return s, abs(term)
                    s += term
            if b - a + 1 == m:
                return s, S.Zero
            a += m
        x = Dummy('x')
        I = Integral(f.subs(i, x), (x, a, b))
        if eval_integral:
            I = I.doit()
        s += I

        def fpoint(expr):
            if b is S.Infinity:
                return expr.subs(i, a), 0
            return expr.subs(i, a), expr.subs(i, b)

        fa, fb = fpoint(f)
        iterm = (fa + fb) / 2
        g = f.diff(i)
        for k in range(1, n + 2):
            ga, gb = fpoint(g)
            term = bernoulli(2 * k) / factorial(2 * k) * (gb - ga)
            if (eps and term and abs(term.evalf(3)) < eps) or (k > n):
                break
            s += term
            g = g.diff(i, 2, simplify=False)
        return s + iterm, abs(term)

    def reverse_order(self, *indices):
        """
        Reverse the order of a limit in a Sum.

        Usage
        =====

        ``reverse_order(self, *indices)`` reverses some limits in the expression
        ``self`` which can be either a ``Sum`` or a ``Product``. The selectors in
        the argument ``indices`` specify some indices whose limits get reversed.
        These selectors are either variable names or numerical indices counted
        starting from the inner-most limit tuple.

        Examples
        ========

        >>> from sympy import Sum
        >>> from sympy.abc import x, y, a, b, c, d

        >>> Sum(x, (x, 0, 3)).reverse_order(x)
        Sum(-x, (x, 4, -1))
        >>> Sum(x*y, (x, 1, 5), (y, 0, 6)).reverse_order(x, y)
        Sum(x*y, (x, 6, 0), (y, 7, -1))
        >>> Sum(x, (x, a, b)).reverse_order(x)
        Sum(-x, (x, b + 1, a - 1))
        >>> Sum(x, (x, a, b)).reverse_order(0)
        Sum(-x, (x, b + 1, a - 1))

        While one should prefer variable names when specifying which limits
        to reverse, the index counting notation comes in handy in case there
        are several symbols with the same name.

        >>> S = Sum(x**2, (x, a, b), (x, c, d))
        >>> S
        Sum(x**2, (x, a, b), (x, c, d))
        >>> S0 = S.reverse_order(0)
        >>> S0
        Sum(-x**2, (x, b + 1, a - 1), (x, c, d))
        >>> S1 = S0.reverse_order(1)
        >>> S1
        Sum(x**2, (x, b + 1, a - 1), (x, d + 1, c - 1))

        Of course we can mix both notations:

        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(x, 1)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))
        >>> Sum(x*y, (x, a, b), (y, 2, 5)).reverse_order(y, x)
        Sum(x*y, (x, b + 1, a - 1), (y, 6, 1))

        See Also
        ========

        index, reorder_limit, reorder

        References
        ==========

        .. [1] Michael Karr, "Summation in Finite Terms", Journal of the ACM,
               Volume 28 Issue 2, April 1981, Pages 305-350
               http://dl.acm.org/citation.cfm?doid=322248.322255
        """
        l_indices = list(indices)

        for i, indx in enumerate(l_indices):
            if not isinstance(indx, int):
                l_indices[i] = self.index(indx)

        e = 1
        limits = []
        for i, limit in enumerate(self.limits):
            l = limit
            if i in l_indices:
                e = -e
                l = (limit[0], limit[2] + 1, limit[1] - 1)
            limits.append(l)

        return Sum(e * self.function, *limits)

    def as_two_terms(self):
        first, second = self.function.as_two_terms()
        first = self.func(first, *self.limits).simplifier()
        second = self.func(second, *self.limits).simplifier()
        if isinstance(self.function, Add):
            return first + second
        else:
#             from sympy.matrices.expressions.hadamard import HadamardProduct
            return first * second

    def simplifier(self):
        from sympy.concrete import summations
#         from sympy.matrices.expressions.hadamard import HadamardProduct
        if isinstance(self.function, summations.Sum) and not self.function.limits and isinstance(self.function.function, Mul):
            (x, *_), *_ = self.limits
            independent, dependent = [], []
            for arg in self.function.function.args:
                if arg.has(x):
                    dependent.append(arg)
                else:
                    independent.append(arg)

            if not dependent:
                return Mul(*independent)
            if not independent:
                return self

            from sympy import Transpose
            from sympy.matrices.expressions.matmul import MatMul
            return MatMul(Mul(*independent), Transpose(self.func(Mul(*dependent), *self.limits).simplifier()).simplifier())

        first, second = self.simplifier_add(self.function)
        if first is None:
            first, second = self.simplifier_mul(self.function)
            if first is None:
                from sympy import exp
                if isinstance(self.function, exp):
                    simplified = self.func(self.function.args[0], *self.limits).simplifier()
                    if not isinstance(simplified, Ref):
                        return exp(simplified)
                return self

            if second is None:
                return first

            return Mul(first, self.func(second, *self.limits).simplifier())

        if second is None:
            return first
        return first + self.func(second, *self.limits).simplifier()

    def simplifier_add(self, exp):
        from sympy.core.basic import Atom
        from sympy.tensor.indexed import Indexed
        x = tuple(x for x, *_ in self.limits)
        if isinstance(exp, Atom):
            return exp, None

        if isinstance(exp, Indexed):
            if exp.args[-len(x):] == tuple(x for x, *_ in self.limits):
                return exp.base[exp.indices[:-len(x)]], None

            return None, exp

        if isinstance(exp, Add):
            argsNonSimplified = []
            argsSimplified = []
            for arg in exp.args:
                simplified, nonSimplified = self.simplifier_add(arg)
                if simplified is not None:
                    argsSimplified.append(simplified)
                if nonSimplified is not None:
                    argsNonSimplified.append(nonSimplified)

            if not argsSimplified:
                argsSimplified = None
            elif len(argsSimplified) == 1:
                argsSimplified = argsSimplified[0]
            else:
                argsSimplified = Add(*argsSimplified)

            if not argsNonSimplified:
                argsNonSimplified = None
            elif len(argsNonSimplified) == 1:
                argsNonSimplified = argsNonSimplified[0]
            else:
                argsNonSimplified = Add(*argsNonSimplified)

            return argsSimplified, argsNonSimplified
#             from sympy import S
        independent, dependent = exp.as_independent(*x, as_Add=True)
        if independent == S.Zero:
            return None, dependent
        if dependent == S.Zero:
            dependent = None
        return independent, dependent

    def simplifier_mul(self, exp):
        (x, *_), *_ = self.limits
#         from sympy.matrices.expressions.matexpr import MatrixElement
        from sympy.core.basic import Atom
        if isinstance(exp, Atom):
            return exp, None

        from sympy.tensor.indexed import Indexed
        if isinstance(exp, Indexed):
            if exp.args[-1] == x:
                return exp.base[exp.indices[:-1]], None

            return None, exp
        if isinstance(exp, Mul):
            argsNonSimplified = []
            argsSimplified = []
            for arg in exp.args:
                simplified, nonSimplified = self.simplifier_mul(arg)
                if simplified is not None:
                    argsSimplified.append(simplified)
                if nonSimplified is not None:
                    argsNonSimplified.append(nonSimplified)

            if not argsSimplified:
                argsSimplified = None
            elif len(argsSimplified) == 1:
                argsSimplified = argsSimplified[0]
            else:
                argsSimplified = Mul(*argsSimplified)

            if not argsNonSimplified:
                argsNonSimplified = None
            elif len(argsNonSimplified) == 1:
                argsNonSimplified = argsNonSimplified[0]
            else:
                argsNonSimplified = Mul(*argsNonSimplified)

            return argsSimplified, argsNonSimplified

#             from sympy import S
        independent, dependent = exp.as_independent(x, as_Add=False)
        if independent == S.One:
            return None, dependent
        if dependent == S.One:
            dependent = None
        return independent, dependent

    def as_Min(self):
        if isinstance(self.function, Minimum) and len(self.function.limits) == 0:
            minimum = self.function
            function = minimum.function
            return minimum.func(self.func(function, *self.limits).simplifier())
        return self

    def __getitem__(self, indices, **kw_args):
        if isinstance(indices, (tuple, list)):
            function = self.function
            for i, index in enumerate(indices):
                x, *_ = self.limits[i]
                function = function.subs(x, index)
            return function
        if isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            x, n = self.limits[0]
            if start > 0:
                function = self.function.subs(x, x + start)
                stop -= start

                if stop >= n:
                    stop = n
                limits = [*self.limits]
                limits[0] = x, stop
                return self.func(function, *limits)

            else:
                if stop >= n:
                    return self
                limits = [*self.limits]
                limits[0] = x, stop
                return self.func(self.function, *limits)

        x, *_ = self.limits[0]
        return self.function.subs(x, indices)

    @property
    def shape(self):
        shape = []
        for limit in self.limits:
            if len(limit) == 1:
                shape.append(limit[0].domain.size)
            else:
                shape.append(limit[1])
        return tuple(shape)

    @property
    def cols(self):
        return self.shape[-1]

    @property
    def rows(self):
        if len(self.shape) == 1:
            return 1
        return self.shape[-2]

    @property
    def is_ZeroMatrix(self):
        return False

    @property
    def is_Matrix(self):
        return len(self.shape) == 2

    @property
    def is_square(self):
        return self.rows == self.cols

    def inverse(self):
        from sympy.matrices.expressions.inverse import Inverse
        return Inverse(self)

    def _eval_determinant(self):
        from sympy.matrices.expressions.determinant import Determinant
        from sympy.concrete.products import Product
        if not self.is_square:
            return None
        if self.is_upper or self.is_lower:
            limit = self.limits[0]
            if len(limit) == 2:
                i, n = limit
                n = n - 1
            elif len(limit) == 1:
                i, *_ = limit
                n = i.domain.end

            return Product(self[i, i], (i, 0, n)).doit()
        return Determinant(self)

    @property
    def is_lower(self):
        """Check if matrix is a lower triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_lower
        True

        >>> m = Matrix(4, 3, [0, 0, 0, 2, 0, 0, 1, 4 , 0, 6, 6, 5])
        >>> m
        Matrix([
        [0, 0, 0],
        [2, 0, 0],
        [1, 4, 0],
        [6, 6, 5]])
        >>> m.is_lower
        True

        >>> from sympy.abc import x, y
        >>> m = Matrix(2, 2, [x**2 + y, y**2 + x, 0, x + y])
        >>> m
        Matrix([
        [x**2 + y, x + y**2],
        [       0,    x + y]])
        >>> m.is_lower
        False

        See Also
        ========

        is_upper
        is_diagonal
        is_lower_hessenberg
        """
        (i, *_), *_ = self.limits
        j = i.generate_free_symbol(domain=Interval(i + 1, self.cols, right_open=True, integer=True))
        return self[i, j] == 0

    @property
    def is_upper(self):
        """Check if matrix is an upper triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_upper
        True

        >>> m = Matrix(4, 3, [5, 1, 9, 0, 4 , 6, 0, 0, 5, 0, 0, 0])
        >>> m
        Matrix([
        [5, 1, 9],
        [0, 4, 6],
        [0, 0, 5],
        [0, 0, 0]])
        >>> m.is_upper
        True

        >>> m = Matrix(2, 3, [4, 2, 5, 6, 1, 1])
        >>> m
        Matrix([
        [4, 2, 5],
        [6, 1, 1]])
        >>> m.is_upper
        False

        See Also
        ========

        is_lower
        is_diagonal
        is_upper_hessenberg
        """
        * _ , (j, *_) = self.limits
        i = j.generate_free_symbol(domain=Interval(j + 1, self.rows, right_open=True, integer=True))
        return self[i, j] == 0

    def _latex(self, p):
        args = []
        for limit in self.limits:
            if len(limit) == 1:
                args.append(p._print(limit[0]))
            elif len(limit) == 2:
                args.append(r"%s:%s" % (p._print(limit[0]), p._print(limit[1])))
            elif len(limit) == 3:
                if limit[1] == 0:
                    args.append(r"%s:%s" % (p._print(limit[0]), p._print(limit[2])))
                else:
                    args.append(r"%s:%s:%s" % (p._print(limit[1]), p._print(limit[0]), p._print(limit[2])))

        tex = r"[%s]" % ','.join(args)

        if isinstance(self.function, (Add, Mul)):
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex


class UnionComprehension(Set, ExprWithLimits):
    """
    Represents a union of sets as a :class:`Set`.

    Examples
    ========

    >>> from sympy import Union, Interval
    >>> Union(Interval(1, 2), Interval(3, 4))
    Union(Interval(1, 2), Interval(3, 4))

    The Union constructor will always try to merge overlapping intervals,
    if possible. For example:

    >>> Union(Interval(1, 2), Interval(2, 3))
    Interval(1, 3)

    See Also
    ========

    Intersection

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Union_%28set_theory%29
    """
    is_UnionComprehension = True

    def assertion(self):

        from sympy.sets.conditionset import ConditionSet
        from sympy.tensor.indexed import Slice

        image_set = self.image_set()
        if image_set is None:
            return

        expr, variables, base_set = image_set
        if isinstance(base_set, Symbol):
            if isinstance(base_set.definition, ConditionSet):
                base_set = base_set.definition
            else:
                return
        else:
            if not isinstance(base_set, ConditionSet):
                return

        sym = base_set.sym
        if isinstance(sym, Symbol):
            ...
        elif isinstance(sym, Slice):
            condition = base_set.condition
            element_symbol = self.element_symbol
            assert expr.dtype == element_symbol.dtype
            return condition.func(*condition.args, forall={element_symbol:self}, exists={variables: Equality(expr, element_symbol)})

    def simplifier(self):
        if len(self.limits) != 1:
            return self
        limit = self.limits[0]

        if len(limit) == 2:
            return self

        if len(limit) > 1:
            x, a, b = limit
            domain = Interval(a, b, integer=True)
            if isinstance(self.function, Piecewise):
                return Union(*self.as_multiple_terms(x, domain))

            if isinstance(domain, FiniteSet):
                args = []
                for k in domain:
                    args.append(self.function.subs(x, k))
                return Union(*args)
            if isinstance(domain, EmptySet):
                return S.EmptySet

            a, b = domain.min(), domain.max()
            limit = x, a, b
        var = limit[0]

        import sympy
        function = self.function
        if isinstance(function, sympy.exp):
            function = function.as_Mul()

        independent, dependent = function.as_independent(var, as_Add=False)
        if independent == S.One:
            if limit != self.limits[0]:
                return self.func(function, limit)
            return self

        if dependent == S.One:
            if len(limit) > 1:
                return self.function * (b - a + 1)
            else:
                return self.function * var.dimension

        return self.func(dependent, limit) * independent

    def union_sets(self, expr):
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b + 1) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))
            elif len(args) == 1:
                domain = args[0]
                if isinstance(domain, Complement):
                    A, B = domain.args
                    if isinstance(B, FiniteSet):
                        deletes = set()
                        for b in B:
                            if self.function.subs(i, b) == expr:
                                deletes.add(b)
                        if deletes:
                            B -= FiniteSet(*deletes)
                            if B:
                                domain = Complement(A, B, evaluate=False)
                                return self.func(self.function, (i, domain))
                            domain = A
                            if isinstance(domain, Interval) and domain.is_integer:
                                return self.func(self.function, (i, domain.min(), domain.max()))
                            return self.func(self.function, (i, domain))

    def _sympystr(self, p):
        limits = ','.join([':'.join([p.doprint(arg) for arg in limit]) for limit in self.limits])
        if limits:
            return 'Union[%s](%s)' % (limits, p.doprint(self.function))
        return 'Union(%s)' % p.doprint(self.function)

    def int_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 3:
            return limit

    def condition_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 2:
            return limit

    def expr_iterable(self):
        function = self.function
        from sympy.tensor.indexed import Indexed

        if isinstance(function, FiniteSet):
            if len(function) == 1:
                expr, *_ = function
                if isinstance(expr, Indexed):
                    return expr.base

                    if len(self.limits) == 1:
                        limit = self.limits[0]
                        return len(limit) == 3

    def image_set(self):
        function = self.function
        if isinstance(function, FiniteSet) and len(function) == 1:
            condition_limit = self.condition_limit()
            if condition_limit  is not None:
                x, condition = condition_limit
                expr, *_ = function
                return expr, x, condition

    def finite_set(self):
        int_limit = self.int_limit()
        if int_limit is not None:
            expr_iterable = self.expr_iterable()
            if expr_iterable is not None:
                _, a, b = int_limit
                return expr_iterable[a:b + 1]

    def _latex(self, p):
        finite_set = self.finite_set()
        if finite_set is not None:
            return r"set\left(%s\right) " % p._print(finite_set)

        image_set = self.image_set()
        if image_set is not None:
            lamda_expr, lamda_variables, base_set = image_set
            from sympy.sets.conditionset import ConditionSet
            if isinstance(base_set, ConditionSet) and lamda_variables == base_set.sym:
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), p._print(base_set.condition))

#             from sympy.core.containers import Tuple
            if isinstance(lamda_variables, Tuple):
                varsets = [r"%s \in %s" % (p._print(var), p._print(setv)) for var, setv in zip(lamda_variables, base_set)]
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), ', '.join(varsets))

            varsets = r"%s \in %s" % (p._print(lamda_variables), p._print(base_set))
            return r"\left\{\left. %s \right| %s \right\}" % (p._print(lamda_expr), varsets)

        function = self.function
        limits = self.limits

        if len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex = r"\bigcup_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                tex = r"\bigcup\limits_{%s \in %s} " % tuple([p._print(i) for i in limit])
            else:
                tex = r"\bigcup\limits_{%s=%s}^{%s} " % tuple([p._print(i) for i in limit])
        else:

            def _format_ineq(l):
                return r"%s \leq %s \leq %s" % \
                    tuple([p._print(s) for s in (l[1], l[0], l[2])])

            tex = r"\bigcup\limits_{\substack{%s}} " % \
                str.join('\\\\', [_format_ineq(l) for l in limits])

        if isinstance(function, Add):
            tex += r"\left(%s\right)" % p._print(function)
        else:
            tex += p._print(function)

        return tex

    @property
    def identity(self):
        return S.EmptySet

    @property
    def zero(self):
        return S.UniversalSet

    def __new__(cls, function, *symbols, **assumptions):
        obj = ExprWithLimits.__new__(cls, function, *symbols, **assumptions)
        return obj

    @property
    def function(self):
        return self.args[0]

    @property
    def limits(self):
        return self.args[1:]

    @property
    @cacheit
    def args(self):
        return self._args

    def _complement(self, universe):
        # DeMorgan's Law
        return Intersection(s.complement(universe) for s in self.args)

    @property
    def _inf(self):
        # We use Min so that sup is meaningful in combination with symbolic
        # interval end points.
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*[set.inf for set in self.args])

    @property
    def _sup(self):
        # We use Max so that sup is meaningful in combination with symbolic
        # end points.
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*[set.sup for set in self.args])

    def _contains(self, other):
        exists = {}
        for limit in self.limits:
            x, *ab = limit
            if len(ab) == 2:
                domain = Interval(*ab, integer=True)
            elif len(ab) == 1:
                domain = ab[0]
            else:
                domain = S.Integers
            exists[x] = domain
        from sympy.sets.contains import Contains
        return Contains(other, self.function, exists=exists)

    @property
    def _measure(self):
        # Measure of a union is the sum of the measures of the sets minus
        # the sum of their pairwise intersections plus the sum of their
        # triple-wise intersections minus ... etc...

        # Sets is a collection of intersections and a set of elementary
        # sets which made up those intersections (called "sos" for set of sets)
        # An example element might of this list might be:
        #    ( {A,B,C}, A.intersect(B).intersect(C) )

        # Start with just elementary sets (  ({A}, A), ({B}, B), ... )
        # Then get and subtract (  ({A,B}, (A int B), ... ) while non-zero
        sets = [(FiniteSet(s), s) for s in self.args]
        measure = 0
        parity = 1
        while sets:
            # Add up the measure of these sets and add or subtract it to total
            measure += parity * sum(inter.measure for sos, inter in sets)

            # For each intersection in sets, compute the intersection with every
            # other set not already part of the intersection.
            sets = ((sos + FiniteSet(newset), newset.intersect(intersection))
                    for sos, intersection in sets for newset in self.args
                    if newset not in sos)

            # Clear out sets with no measure
            sets = [(sos, inter) for sos, inter in sets if inter.measure != 0]

            # Clear out duplicates
            sos_list = []
            sets_list = []
            for set in sets:
                if set[0] in sos_list:
                    continue
                else:
                    sos_list.append(set[0])
                    sets_list.append(set)
            sets = sets_list

            # Flip Parity - next time subtract/add if we added/subtracted here
            parity *= -1
        return measure

    @property
    def _boundary(self):

        def boundary_of_set(i):
            """ The boundary of set i minus interior of all other sets """
            b = self.args[i].boundary
            for j, a in enumerate(self.args):
                if j != i:
                    b = b - a.interior
            return b

        return Union(*map(boundary_of_set, range(len(self.args))))

    def as_relational(self, symbol):
        """Rewrite a Union in terms of equalities and logic operators. """
        if len(self.args) == 2:
            a, b = self.args
            if (a.sup == b.inf and a.inf is S.NegativeInfinity
                    and b.sup is S.Infinity):
                return And(Ne(symbol, a.sup), symbol < b.sup, symbol > a.inf)
        return Or(*[set.as_relational(symbol) for set in self.args])

    @property
    def is_iterable(self):
        return all(arg.is_iterable for arg in self.args)

    def _eval_evalf(self, prec):
        try:
            return Union(*(set._eval_evalf(prec) for set in self.args))
        except (TypeError, ValueError, NotImplementedError):
            import sys
            raise (TypeError("Not all sets are evalf-able"),
                   None,
                   sys.exc_info()[2])

    def __iter__(self):
        import itertools

        # roundrobin recipe taken from itertools documentation:
        # https://docs.python.org/2/library/itertools.html#recipes
        def roundrobin(*iterables):
            "roundrobin('ABC', 'D', 'EF') --> A D E B F C"
            # Recipe credited to George Sakkis
            pending = len(iterables)
            if PY3:
                nexts = itertools.cycle(iter(it).__next__ for it in iterables)
            else:
                nexts = itertools.cycle(iter(it).next for it in iterables)
            while pending:
                try:
                    for next in nexts:
                        yield next()
                except StopIteration:
                    pending -= 1
                    nexts = itertools.cycle(itertools.islice(nexts, pending))

        if all(set.is_iterable for set in self.args):
            return roundrobin(*(iter(arg) for arg in self.args))
        else:
            raise TypeError("Not all constituent sets are iterable")

    @property
    def is_integer(self):
        for arg in self.args:
            is_integer = arg.is_integer
            if is_integer is True:
                continue
            if is_integer is False:
                return False
            return None
        return True

    @property
    def element_type(self):
        return self.function.element_type
