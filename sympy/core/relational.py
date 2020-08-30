from __future__ import print_function, division

from .add import _unevaluated_Add, Add
from .basic import S
from .compatibility import ordered
from .expr import Expr
from .evalf import EvalfMixin
from .sympify import _sympify
from .evaluate import global_evaluate

from sympy.logic.boolalg import Boolean, BooleanAtom
from sympy.core.sympify import sympify
from sympy.core.basic import preorder_traversal

__all__ = (
    'Rel', 'Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge',
    'Relational', 'Equality', 'Unequality', 'StrictLessThan', 'LessThan',
    'StrictGreaterThan', 'GreaterThan',
)

# Note, see issue 4986.  Ideally, we wouldn't want to subclass both Boolean
# and Expr.


def _canonical(cond):
    # return a condition in which all relationals are canonical
    reps = {r: r.canonical for r in cond.atoms(Relational)}
    return cond.xreplace(reps)
    # XXX: AttributeError was being caught here but it wasn't triggered by any of
    # the tests so I've removed it...


# from sympy.logic.boolalg import Boolean
class Relational(Boolean, Expr, EvalfMixin):
    """Base class for all relation types.

    Subclasses of Relational should generally be instantiated directly, but
    Relational can be instantiated with a valid `rop` value to dispatch to
    the appropriate subclass.

    Parameters
    ==========
    rop : str or None
        Indicates what subclass to instantiate.  Valid values can be found
        in the keys of Relational.ValidRelationalOperator.

    Examples
    ========

    >>> from sympy import Rel
    >>> from sympy.abc import x, y
    >>> Rel(y, x + x**2, '==')
    Eq(y, x**2 + x)

    """
    __slots__ = []

    is_Relational = True

    _op_priority = 12  # higher than Expr
    # ValidRelationOperator - Defined below, because the necessary classes
    #   have not yet been defined

    def comprehension(self, operator, *limits, func=None):
        lhs = operator(self.lhs, *limits).simplify()
        rhs = operator(self.rhs, *limits).simplify()
        this = self.func(lhs, rhs)

        if func:
            from sympy.concrete import expr_with_limits
            dic = expr_with_limits.limits_dict(limits)
            for f, limits in func:
                _dic = expr_with_limits.limits_dict(limits)
                keys = dic.keys() & _dic.keys()
                if keys:
                    for k in keys:
                        if dic[k] not in _dic[k]:
                            return self
                    limits = expr_with_limits.limits_delete(limits, keys)
                    if not limits:
                        continue
                this = f(this, *limits).simplify()

        return this

    @property
    def atomic_dtype(self):
        from sympy.core.symbol import dtype
        return dtype.condition

    def __new__(cls, lhs, rhs, rop=None, **assumptions):

        # If called by a subclass, do nothing special and pass on to Expr.

        if cls is not Relational:
            return Boolean.__new__(cls, lhs, rhs, **assumptions)
        # If called directly with an operator, look up the subclass
        # corresponding to that operator and delegate to it
        try:
            cls = cls.ValidRelationOperator[rop]
            rv = cls(lhs, rhs, **assumptions)
            # /// drop when Py2 is no longer supported
            # validate that Booleans are not being used in a relational
            # other than Eq/Ne;
            if isinstance(rv, (Eq, Ne)):
                pass
            elif isinstance(rv, Relational):  # could it be otherwise?
                from sympy.core.symbol import Symbol

                for a in rv.args:
                    if isinstance(a, Symbol):
                        continue
                    if isinstance(a, Boolean):
                        from sympy.utilities.misc import filldedent
                        raise TypeError(filldedent('''
                            A Boolean argument can only be used in
                            Eq and Ne; all other relationals expect
                            real expressions.
                        '''))
            # \\\
            return rv
        except KeyError:
            raise ValueError(
                "Invalid relational operator symbol: %r" % rop)

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    @property
    def reversed(self):
        """Return the relationship with sides reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.reversed
        Eq(1, x)
        >>> x < 1
        x < 1
        >>> _.reversed
        1 > x
        """
        a, b = self.args
        return self.reversed_type(b, a, equivalent=self, evaluate=False)

    def __neg__(self):
        """Return the relationship with signs reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.neg
        Eq(-x, -1)
        >>> x < 1
        x < 1
        >>> _.neg
        -x > -1
        """

        return self.reversed_type(-self.lhs, -self.rhs, equivalent=self)

    def _eval_evalf(self, prec):
        return self.func(*[s._evalf(prec) for s in self.args])

    @property
    def canonical(self):
        """Return a canonical form of the relational by putting a
        Number on the rhs else ordering the args. The relation is also changed
        so that the left-hand side expression does not start with a `-`.
        No other simplification is attempted.

        Examples
        ========

        >>> from sympy.abc import x, y
        >>> x < 2
        x < 2
        >>> _.reversed.canonical
        x < 2
        >>> (-y < x).canonical
        x > -y
        >>> (-y > x).canonical
        x < -y
        """
        args = self.args
        r = self
        if r.rhs.is_number:
            if r.rhs.is_Number and r.lhs.is_Number and r.lhs > r.rhs:
                r = r.reversed
        elif r.lhs.is_number:
            r = r.reversed
        elif tuple(ordered(args)) != args:
            r = r.reversed

        # Check if first value has negative sign
        if not isinstance(r.lhs, BooleanAtom) and \
                r.lhs.could_extract_minus_sign():
            r = -r
        elif not isinstance(r.rhs, BooleanAtom) and not r.rhs.is_number and \
                r.rhs.could_extract_minus_sign():
            # Right hand side has a minus, but not lhs.
            # How does the expression with reversed signs behave?
            # This is so that expressions of the type Eq(x, -y) and Eq(-x, y)
            # have the same canonical representation
            expr1, _ = ordered([r.lhs, -r.rhs])
            if expr1 != r.lhs:
                r = -r.reversed
        return r

    def equals(self, other, failing_expression=False):
        """Return True if the sides of the relationship are mathematically
        identical and the type of relationship is the same.
        If failing_expression is True, return the expression whose truth value
        was unknown."""
        if isinstance(other, Relational):
            if self == other or self.reversed == other:
                return True
            a, b = self, other
            if a.func in (Eq, Ne) or b.func in (Eq, Ne):
                if a.func != b.func:
                    return False
                left, right = [i.equals(j,
                                        failing_expression=failing_expression)
                               for i, j in zip(a.args, b.args)]
                if left is True:
                    return right
                if right is True:
                    return left
                lr, rl = [i.equals(j, failing_expression=failing_expression)
                          for i, j in zip(a.args, b.reversed.args)]
                if lr is True:
                    return rl
                if rl is True:
                    return lr
                e = (left, right, lr, rl)
                if all(i is False for i in e):
                    return False
                for i in e:
                    if i not in (True, False):
                        return i
            else:
                if b.func != a.func:
                    b = b.reversed
                if a.func != b.func:
                    return False
                left = a.lhs.equals(b.lhs,
                                    failing_expression=failing_expression)
                if left is False:
                    return False
                right = a.rhs.equals(b.rhs,
                                     failing_expression=failing_expression)
                if right is False:
                    return False
                if left is True:
                    return right
                return left

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.simplify import simplify
        r = self
        r = r.func(*[simplify(i, ratio=ratio, measure=measure, rational=rational, inverse=inverse) for i in r.args])
        if r.is_Relational:
            dif = r.lhs - r.rhs
            # replace dif with a valid Number that will
            # allow a definitive comparison with 0
            v = None
            if dif.is_comparable:
                v = dif.n(2)
            elif dif.equals(0):  # XXX this is expensive
                v = S.Zero
            if v is not None:
                r = r.func._eval_relation(v, S.Zero)

        r = r.canonical
        if measure(r) < ratio * measure(self):
            return r
        else:
            return self

    def _eval_trigsimp(self, **opts):
        from sympy.simplify import trigsimp
        return self.func(trigsimp(self.lhs, **opts), trigsimp(self.rhs, **opts))

    def __nonzero__(self):
        return False
        raise TypeError("cannot determine truth value of Relational")

    __bool__ = __nonzero__

    def _eval_as_set(self):
        # self is univariate and periodicity(self, x) in (0, None)
        from sympy.solvers.inequalities import solve_univariate_inequality
        syms = self.free_symbols
        assert len(syms) == 1
        x = syms.pop()
        return solve_univariate_inequality(self, x, relational=False)

    @property
    def binary_symbols(self):
        # override where necessary
        return set()

    @property
    def definition(self):
        if 'definition' in self._assumptions:
            return self._assumptions['definition']
        return None

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return Boolean.simplify(self, deep=True, wrt=wrt)        

        lhs, rhs = self.args
        from sympy.core.mul import Mul
        lhs_func = lhs.func
        rhs_func = rhs.func
        if lhs_func == rhs_func == Add:
            lhs_args = [*lhs.args]
            rhs_args = [*rhs.args]
            intersect = set(lhs_args) & set(rhs_args)
            if intersect:
                for arg in intersect:
                    lhs_args.remove(arg)
                    rhs_args.remove(arg)
                return self.func(lhs_func(*lhs_args), rhs_func(*rhs_args), equivalent=self).simplify()
        elif rhs_func == Add:
            rhs_args = [*rhs.args]
            if lhs in rhs_args:
                rhs_args.remove(lhs)
                return self.func(0, rhs_func(*rhs_args), equivalent=self).simplify()
        elif lhs_func == Add:
            lhs_args = [*lhs.args]
            if rhs in lhs_args:
                lhs_args.remove(rhs)
                return self.func(lhs_func(*lhs_args), 0, equivalent=self).simplify()
            
        from sympy import Symbol
        if not lhs._has(Symbol) and rhs._has(Symbol):
            return self.reversed
        return self

    def expand(self, *args, **kwargs):
        return self.func(self.lhs.expand(*args, **kwargs), self.rhs.expand(*args, **kwargs), equivalent=self)

    def doit(self, *args, **kwargs):
        return self.func(self.lhs.doit(*args, **kwargs), self.rhs.doit(*args, **kwargs), equivalent=self)

    def __add__(self, exp):
        if isinstance(exp, Equality):
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
        elif isinstance(exp, Relational):
            return exp.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
        elif exp.is_ConditionalBoolean:
            return self.bfn(self.__add__, exp)
        else:
            return self.func(self.lhs + exp, self.rhs + exp, equivalent=self)

    def __sub__(self, exp):
        if isinstance(exp, Equality):
            return self.func(self.lhs - exp.lhs, self.rhs - exp.rhs, equivalent=[self, exp])
        elif exp.is_ConditionalBoolean:
            return self.bfn(self.__sub__, exp)
        else:
            return self.func(self.lhs - exp, self.rhs - exp, equivalent=self)

    def __mul__(self, exp):
        if isinstance(exp, Equality):
            if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
            return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])

        else:
            if exp > 0:
                return self.func(self.lhs * exp, self.rhs * exp, equivalent=self)
            if exp < 0:
                return self.reversed_type(self.lhs * exp, self.rhs * exp, equivalent=self)
            elif exp >= 0:
                return self.func(self.lhs * exp, self.rhs * exp, given=self)
            elif exp <= 0:
                return self.reversed_type(self.lhs * exp, self.rhs * exp, given=self)
            return self

    def __truediv__(self, exp):
        if isinstance(exp, Equality):
            if exp.lhs != 0 or exp.rhs != 0:
                return self.func(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=[self, exp])
            return self
        else:
            if exp > 0:
                return self.func((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self)
            if exp < 0:
                return self.reversed_type((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self)
            return self

    def __iter__(self):
        raise TypeError

    def domain_defined(self, x):
        return self.lhs.domain_defined(x) & self.rhs.domain_defined(x)

    def solve(self, x):
        from sympy.sets.contains import Contains
        if not x.is_Symbol:
            _x = self.generate_free_symbol(x.free_symbols, **x.dtype.dict)
            this = self._subs(x, _x)
            domain = _x.domain_conditioned(this)            
            domain = domain._subs(_x, x)
        else:
            domain = x.domain_conditioned(self)
            
        if domain.is_ConditionSet:
            self
            
        return Contains(x, domain, equivalent=self).simplify()

    def is_positive_relationship(self):
        ...

            
Rel = Relational


class Equality(Relational):
    """An equal relation between two objects.

    Represents that two objects are equal.  If they can be easily shown
    to be definitively equal (or unequal), this will reduce to True (or
    False).  Otherwise, the relation is maintained as an unevaluated
    Equality object.  Use the ``simplify`` function on this object for
    more nontrivial evaluation of the equality relation.

    As usual, the keyword argument ``evaluate=False`` can be used to
    prevent any evaluation.

    Examples
    ========

    >>> from sympy import Eq, simplify, exp, cos
    >>> from sympy.abc import x, y
    >>> Eq(y, x + x**2)
    Eq(y, x**2 + x)
    >>> Eq(2, 5)
    False
    >>> Eq(2, 5, evaluate=False)
    Eq(2, 5)
    >>> _.doit()
    False
    >>> Eq(exp(x), exp(x).rewrite(cos))
    Eq(exp(x), sinh(x) + cosh(x))
    >>> simplify(_)
    True

    See Also
    ========

    sympy.logic.boolalg.Equivalent : for representing equality between two
        boolean expressions

    Notes
    =====

    This class is not the same as the == operator.  The == operator tests
    for exact structural equality between two expressions; this class
    compares expressions mathematically.

    If either object defines an `_eval_Eq` method, it can be used in place of
    the default algorithm.  If `lhs._eval_Eq(rhs)` or `rhs._eval_Eq(lhs)`
    returns anything other than None, that return value will be substituted for
    the Equality.  If None is returned by `_eval_Eq`, an Equality object will
    be created as usual.

    Since this object is already an expression, it does not respond to
    the method `as_expr` if one tries to create `x - y` from Eq(x, y).
    This can be done with the `rewrite(Add)` method.
    """
    rel_op = '=='

    __slots__ = []

    is_Equality = True

    @staticmethod
    def continuity(f, a, b):
        from sympy.concrete.expr_with_limits import ForAll
        from sympy import Symbol, Limit
        xi = Symbol('xi', real=True)
        z = Symbol('z', real=True)
        return ForAll(Equality(Limit(f(z), z, xi, '+-'), f(xi)), (xi, a, b))
        
    def strip(self):
        from sympy.concrete.expr_with_limits import ForAll
        if self.lhs.func == self.rhs.func:
            if len(self.lhs.args) == 1:
                condition = self.func(self.lhs.arg, self.rhs.arg)
                if self.lhs.is_FiniteSet:
                    condition.equivalent = self
                else:
                    condition.imply = self
                return condition
            if self.lhs.is_ExprWithLimits:
                return ForAll(self.func(self.lhs.function, self.rhs.function), *self.lhs.limits, imply=self)

        return self

    def __sub__(self, exp):
        if exp.is_Relational:
            return exp.reversed_type(self.lhs - exp.lhs, self.rhs - exp.rhs, equivalent=[self, exp])
        return Relational.__sub__(self, exp)

    def __new__(cls, lhs, rhs=None, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)

        evaluate = options.pop('evaluate', global_evaluate[0])

        if evaluate:
            # If one expression has an _eval_Eq, return its results.
            if hasattr(lhs, '_eval_Eq'):
                r = lhs._eval_Eq(rhs)
                if isinstance(r, BooleanAtom):
                    return r.copy(**options)
            if hasattr(rhs, '_eval_Eq'):
                r = rhs._eval_Eq(lhs)
                if isinstance(r, BooleanAtom):
                    return r.copy(**options)
            # If expressions have the same structure, they must be equal.
            if lhs == rhs or lhs.dummy_eq(rhs):
                return S.true.copy(**options)  # e.g. True == True
            elif all(isinstance(i, BooleanAtom) for i in (rhs, lhs)):
                return S.false  # True != False
            elif not (lhs.is_Symbol or rhs.is_Symbol) and (isinstance(lhs, Boolean) != isinstance(rhs, Boolean)):
                return S.false  # only Booleans can equal Booleans
            from sympy import Contains
            if Contains(rhs, lhs.domain).is_BooleanFalse or Contains(lhs, rhs.domain).is_BooleanFalse:
                return S.false.copy(**options)

            if isinstance(lhs, Expr) and isinstance(rhs, Expr) and not lhs.is_set and not rhs.is_set:
                # see if the difference evaluates
                dif = (lhs - rhs).simplify()
                z = dif.is_zero
                if z is not None:
#                     if z is False and dif.is_commutative:  # issue 10728
                    if z is False:  # issue 10728
                        return S.false.copy(**options)
                    if z:
                        if 'plausible' in options:
                            del options['plausible']
                        else:
                            return S.true.copy(**options)

        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs == rhs)

    def _eval_rewrite_as_Add(self, *args, **kwargs):
        """return Eq(L, R) as L - R. To control the evaluation of
        the result set pass `evaluate=True` to give L - R;
        if `evaluate=None` then terms in L and R will not cancel
        but they will be listed in canonical order; otherwise
        non-canonical args will be returned.

        Examples
        ========

        >>> from sympy import Eq, Add
        >>> from sympy.abc import b, x
        >>> eq = Eq(x + b, x - b)
        >>> eq.rewrite(Add)
        2*b
        >>> eq.rewrite(Add, evaluate=None).args
        (b, b, x, -x)
        >>> eq.rewrite(Add, evaluate=False).args
        (b, x, b, -x)
        """
        L, R = args
        evaluate = kwargs.get('evaluate', True)
        if evaluate:
            # allow cancellation of args
            return L - R
        args = Add.make_args(L) + Add.make_args(-R)
        if evaluate is None:
            # no cancellation, but canonical
            return _unevaluated_Add(*args)
        # no cancellation, not canonical
        return Add._from_args(args)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return set([self.lhs])
            elif self.rhs.is_Symbol:
                return set([self.rhs])
        return set()

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.solvers.solveset import linear_coeffs
        # standard simplify
        e = super(Equality, self)._eval_simplify(
            ratio, measure, rational, inverse)
        if not isinstance(e, Equality):
            return e
        free = self.free_symbols
        if len(free) == 1:
            try:
                x = free.pop()
                m, b = linear_coeffs(
                    e.rewrite(Add, evaluate=False), x)
                if m.is_zero is False:
                    enew = e.func(x, -b / m)
                else:
                    enew = e.func(m * x, -b)
                if measure(enew) <= ratio * measure(e):
                    e = enew
            except ValueError:
                pass
        return e.canonical

    def __truediv__(self, exp):
        if isinstance(exp, Equality):
            if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                return self.func((self.lhs / exp.lhs).ratsimp(), (self.rhs / exp.rhs).ratsimp(), equivalent=[self, exp])
            return self
        else:
            if exp.is_nonzero:
                return self.func((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self)
            return self

    def __mul__(self, exp):
        exp = sympify(exp)
        if isinstance(exp, Equality):
            if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
            return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])

        elif isinstance(exp, StrictLessThan):
            if exp.lhs > 0:
                return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
            elif exp.lhs >= 0:
                if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=self)

            elif exp.rhs < 0:
                if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])

            elif exp.rhs <= 0:
                if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])

            return self
        else:
            if exp.is_nonzero:
                return Eq(self.lhs * exp, self.rhs * exp, equivalent=self)
            return Eq(self.lhs * exp, self.rhs * exp, given=self)

    def __rmatmul__(self, lhs):
        from sympy.matrices.expressions.determinant import det
        if isinstance(lhs, Equality):
            if det(lhs.lhs).is_nonzero or det(lhs.rhs).is_nonzero:
                return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, equivalent=[self, lhs])
            return Eq(lhs.lhs @ self.lhs, lhs.rhs @ self.rhs, given=[self, lhs])
        else:
            if det(lhs).is_nonzero:
                return Eq(lhs @ self.lhs, lhs @ self.rhs, equivalent=self)
            return Eq(lhs @ self.lhs, lhs @ self.rhs, given=self)

    def __matmul__(self, rhs):
        from sympy.matrices.expressions.determinant import det
        if isinstance(rhs, Equality):
            if rhs.lhs.is_square and det(rhs.lhs).is_nonzero or rhs.rhs.is_square and det(rhs.rhs).is_nonzero:
                return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, equivalent=[self, rhs])
            return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, given=[self, rhs])

        else:             
            if rhs.is_square and det(rhs).is_nonzero:
                return self.func(self.lhs @ rhs, self.rhs @ rhs, equivalent=self)
            return self.func(self.lhs @ rhs, self.rhs @ rhs, given=self)

    def __rpow__(self, exp):
        if exp.is_positive:
            return self.func(exp ** self.lhs, exp ** self.rhs, equivalent=self)
        
        if self.lhs.is_positive or self.rhs.is_positive:
            return self.func(exp ** self.lhs, exp ** self.rhs, given=self)
        
        return self    

    def __pow__(self, exp):
        exp = sympify(exp)
        if exp.is_positive:
            return self.func(self.lhs ** exp, self.rhs ** exp, given=self)
        return self
        
    def union(self, exp):
        exp = sympify(exp)
        if isinstance(exp, Equality):
            return self.func(self.lhs | exp.lhs, self.rhs | exp.rhs, given=[self, exp])
        elif exp.is_ConditionalBoolean:
            return self.bfn(self.union, exp)
        else:
            return Eq(self.lhs | exp, self.rhs | exp, given=self)

    def intersect(self, exp):
        exp = sympify(exp)
        if isinstance(exp, Equality):
            return self.func(self.lhs & exp.lhs, self.rhs & exp.rhs, given=[self, exp])
        elif exp.is_ConditionalBoolean:
            return self.bfn(self.intersect, exp)
        else:
            return Eq(self.lhs & exp, self.rhs & exp, given=self)

    def powsimp(self, *args, **kwargs):
        return Eq(self.lhs.powsimp(*args, **kwargs), self.rhs.powsimp(*args, **kwargs), equivalent=self)

    def collect(self, syms):
        return Eq(self.lhs.collect(syms), self.rhs.collect(syms), equivalent=self)

    def sqrt(self):
        from sympy import sqrt
        return self.func(sqrt(self.lhs), sqrt(self.rhs), given=self)

    def abs(self):
        return self.func(abs(self.lhs), abs(self.rhs), given=self)

    def real_root(self, n):
        from sympy import real_root
        return self.func(real_root(self.lhs, n), real_root(self.rhs, n), equivalent=self)

    def rsolve(self, y):
        from sympy.solvers.recurr import rsolve
        solution = rsolve(self, y, symbols=True)
        if solution is None:
            return self
        solution, limits = solution
        
        eq = self.func(y, solution)
        if len(limits) == 0:
            eq.equivalent = self
            return eq
        from sympy.concrete.expr_with_limits import Exists
        for i, C in enumerate(limits):
            limits[i] = (C,)
        return Exists(eq, *limits, equivalent=self)

    def solve(self, x):
        from sympy.solvers.solvers import solve
        res = solve(self.lhs - self.rhs, x)

        if len(res) == 1:
            x_sol, *_ = res
            return Eq(x, x_sol, equivalent=self)
        if len(res) > 1:
            from sympy.logic.boolalg import Or
            return Or(*(Equality(x, x_sol, equivalent=self) for x_sol in res))

        return self

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            arg = args[0]
            if isinstance(arg, dict):
                if 'simultaneous' in kwargs:
                    if self.plausible:
                        return self
                    return self.func(self.lhs.subs(*args, **kwargs).simplify(), self.rhs.subs(*args, **kwargs).simplify()).simplify()
                else:
                    subs = self
                    for key, value in arg.items():
                        subs = subs.subs(key, value)
                    return subs
            elif isinstance(arg, Equality):
                eq = arg
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs).simplify()).simplify().overwrite(self, equivalent=[self, eq])
            elif isinstance(arg, Relational):
                eq = arg
                old, new = eq.args
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)
                if lhs.is_set:
                    if lhs == rhs:
                        return S.false.copy(equivalent=[self, eq])
                    return self
                delta = (lhs - rhs) - (self.lhs - self.rhs)
                match = eq.lhs - eq.rhs

                if delta == match:
                    return arg.func(lhs, rhs, equivalent=[self, eq])
                elif delta == -match:
                    return arg.reversed_type(lhs, rhs, equivalent=[self, eq])
                else:
                    return self
            elif arg.is_ConditionalBoolean:
                return self.bfn(self.subs, arg)
            else:
                return self

        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        old, new = args
        
        from sympy import Symbol
        if not isinstance(old, Symbol):
            lhs = self.lhs.subs(old, new)
            rhs = self.rhs.subs(old, new)

            if lhs == self.lhs and rhs == self.rhs:
                return self
            g = self.lhs - self.rhs
            _g = lhs - rhs
            if _g < g:
                return StrictLessThan(lhs, rhs, given=self)
            if _g <= g:
                return LessThan(lhs, rhs, given=self)

            if _g > g:
                return StrictGreaterThan(lhs, rhs, given=self)
            if _g >= g:
                return GreaterThan(lhs, rhs, given=self)

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = self.func(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self)
            else:
                eq = self.func(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            if isinstance(new, Symbol) and self._has(new):
                from sympy.core.symbol import Dummy
                d = Dummy(**new.dtype.dict)
                this = self.subs(old, d)
                this = this.subs(new, old)
                return this.subs(d, new)
            else:
                return self.func(self.lhs.subs(*args, **kwargs).simplify(), self.rhs.subs(*args, **kwargs).simplify())

    @staticmethod
    def define(x, expr, given=None):
        from sympy.tensor.indexed import Indexed, Slice
        from sympy.core.symbol import Symbol
        from sympy.concrete.expr_with_limits import Exists
        if isinstance(x, (Symbol, Slice)):
            expr = sympify(expr)            
            if not expr.has(x):
                return Exists(Eq(x, expr), (x,))
        elif isinstance(x, Indexed):
            expr = sympify(expr)            
            if expr.has(x.base):
                indices = set()
                for e in preorder_traversal(expr):
                    if isinstance(e, Indexed) and e.base == x.base:
                        if e.indices >= x.indices:
                            return
                        if len(x.indices) < len(e.indices):
                            indices.add(e.indices[:len(x.indices)])
                        else:
                            indices.add(e.indices)
                if given is None or not given.is_Exists or len(given.limits) != 1:
                    return
                limit = given.limits[0]
                if len(limit) != 1:
                    return
                _x = limit[0]
                if not isinstance(_x, Indexed) or _x.base != x.base or _x.indices >= x.indices: 
                    return
                
                return Exists(Eq(x, expr), (x.base,))
            return Exists(Eq(x, expr), (x,))

    def __getitem__(self, indices):
        from sympy.concrete.expr_with_limits import ForAll
        if isinstance(indices, slice):
            x, *args = indices.start, indices.stop, indices.step
            if x.is_bounded:
                x = x.unbounded
            m = self.lhs.shape[0]
            is_equivalent = False
            if len(args) == 2:
                if args[0] == 0 and args[1] == m:
                    is_equivalent = True
            else:
                assert len(args) == 1
                if args[0] == m:
                    is_equivalent = True
            if is_equivalent :
                return self.func(self.lhs[x], self.rhs[x], equivalent=self)
            else:
                ForAll(self.func(self.lhs[x], self.rhs[x]), (x, *args), given=self)
        return self.func(self.lhs[indices], self.rhs[indices], given=self)

    @property
    def set(self):
        return self.func(self.lhs.set, self.rhs.set, equivalent=self)

    def log(self):
        from sympy import log
        return self.func(log(self.lhs), log(self.rhs), equivalent=self)

    def exp(self):
        from sympy import exp
        return self.func(exp(self.lhs), exp(self.rhs), equivalent=self)

    def combsimp(self, *args):
        from sympy import combsimp
        return self.func(combsimp(self.lhs, *args), combsimp(self.rhs, *args), equivalent=self)

    def det(self):
        from sympy import det
        return self.func(det(self.lhs), det(self.rhs), given=self)

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return Boolean.simplify(self, deep=True, wrt=wrt)        

        lhs, rhs = self.args
        from sympy import Mul, MatMul
        from sympy.concrete.expr_with_limits import Ref, ForAll
        from sympy.core.function import _coeff_isneg
        
        if type(lhs) == type(rhs):
            op = lhs.func
            if op == Add:
                lhs_args = [*lhs.args]
                rhs_args = [*rhs.args]
                intersect = set(lhs_args) & set(rhs_args)
                if intersect:
                    for arg in intersect:
                        lhs_args.remove(arg)
                        rhs_args.remove(arg)
                    return self.func(op(*lhs_args), op(*rhs_args), equivalent=self).simplify()
            if op == Mul:
                lhs_args = [*lhs.args]
                rhs_args = [*rhs.args]
                intersect = set(lhs_args) & set(rhs_args)
                if intersect:
                    hit = False
                    for arg in intersect:
                        if arg.is_nonzero:
                            lhs_args.remove(arg)
                            rhs_args.remove(arg)
                            hit = True
                    if hit:
                        return self.func(op(*lhs_args), op(*rhs_args), equivalent=self).simplify()            
            if op == Ref:
                if lhs.limits == rhs.limits:
                    return ForAll(self.func(lhs.function, rhs.function), *lhs.limits, equivalent=self)
            if op == MatMul:
                lhs_args = [*lhs.args]
                rhs_args = [*rhs.args]
                intersect = set(lhs_args) & set(rhs_args)
                if intersect:
                    hit = False
                    for arg in intersect:
                        if arg.is_invertible:
                            lhs_args.remove(arg)
                            rhs_args.remove(arg)
                            hit = True
                    if hit:
                        return self.func(op(*lhs_args), op(*rhs_args), equivalent=self).simplify()
                                     
        elif type(lhs) == Add and rhs in lhs.args:
            args = [*lhs.args]
            args.remove(rhs)
            return self.func(Add(*args), 0, equivalent=self).simplify()
        elif type(rhs) == Add and lhs in rhs.args:
            args = [*rhs.args]
            args.remove(lhs)
            return self.func(0, Add(*args), equivalent=self).simplify()
        elif lhs == 0 and _coeff_isneg(rhs):
            return self.func(0, -rhs, equivalent=self)
        elif rhs == 0 and _coeff_isneg(lhs):
            return self.func(-lhs, 0, equivalent=self)
        elif lhs.is_Piecewise:
            if rhs.is_Piecewise:
                ...
            else:
                cond = lhs.select_cond(rhs)
                if cond is not None:
                    return cond.copy(equivalent=self)
                
        elif rhs.is_Piecewise:
            cond = rhs.select_cond(lhs)
            if cond is not None:
                return cond.copy(equivalent=self)
        elif lhs.is_Intersection and rhs.is_EmptySet:
            this = self.simplify_Intersection(lhs)
            if this is not None:
                return this
        elif rhs.is_Intersection and lhs.is_EmptySet:
            this = self.simplify_Intersection(rhs)
            if this is not None:
                return this
            
        return self

    def simplify_Intersection(self, lhs):
        if len(lhs.args) == 2:
            A, B = lhs.args
            if A.is_FiniteSet and B.is_FiniteSet:
                if len(A) == len(B) == 1:
                    return Unequality(A.arg, B.arg, equivalent=self)
        
    def as_two_terms(self):
        return self.func(self.lhs.as_two_terms(), self.rhs.as_two_terms(), equivalent=self).simplify()

    def split(self, variable=None):
        from sympy.functions.elementary.piecewise import Piecewise
        from sympy.concrete.expr_with_limits import ForAll
        if isinstance(self.rhs, Piecewise):
            if variable is None:
                variables = self.lhs.free_symbols & self.rhs.scope_variables
                if len(variables) > 1:
                    return self
                variable, *_ = variables
            univeralSet = S.BooleanTrue
            args = []

            for expr, condition in self.rhs.args:
                condition = condition & univeralSet
                univeralSet = condition.invert() & univeralSet

                args.append(ForAll(self.func(self.lhs, expr), (variable, condition), given=self).simplify())

            return args

        if isinstance(self.lhs, Piecewise):
            if variable is None:
                variables = self.rhs.free_symbols & self.lhs.scope_variables
                if len(variables) > 1:
                    return self
                variable, *_ = variables
            univeralSet = S.BooleanTrue
            args = []

            for expr, condition in self.lhs.args:
                condition = condition & univeralSet
                univeralSet = condition.invert() & univeralSet
                args.append(ForAll(self.func(expr, self.rhs), (variable, condition), given=self).simplify())

            return args

        return self

    def diff(self, *symbols):
        from sympy.core.function import Derivative
        return self.func(Derivative(self.lhs, *symbols), Derivative(self.rhs, *symbols), given=self)

    def transpose(self):
        return self.func(self.lhs.T, self.rhs.T, equivalent=self)
    
    T = property(transpose, None, None, 'Matrix transposition.')

    def __and__(self, other):
        """Overloading for & operator"""
        if isinstance(other, (StrictLessThan, StrictGreaterThan)):
            if set(self.args) == set(other.args):
                return S.false.copy(given=[self, other])

        return Relational.__and__(self, other)

    def asKroneckerDelta(self):
        from sympy.functions.special.tensor_functions import KroneckerDelta
        return KroneckerDelta(*self.args)

    def conclude(self):
        from sympy import Exists
        if self.lhs.is_Det:
            if self.rhs.is_nonzero:                
                C = self.lhs.generate_free_symbol(singular=False, **self.lhs.arg.dtype.dict)
                return Exists[C](self.func(self.lhs.arg, C), given=self)
        if self.rhs.is_Det:
            if self.lhs.is_nonzero:
                C = self.lhs.generate_free_symbol(singular=False, **self.rhs.arg.dtype.dict)
                return Exists[C](self.func(self.rhs.arg, C), given=self)
        return self


Eq = Equality


class Unequality(Relational):
    """An unequal relation between two objects.

    Represents that two objects are not equal.  If they can be shown to be
    definitively equal, this will reduce to False; if definitively unequal,
    this will reduce to True.  Otherwise, the relation is maintained as an
    Unequality object.

    Examples
    ========

    >>> from sympy import Ne
    >>> from sympy.abc import x, y
    >>> Ne(y, x+x**2)
    Ne(y, x**2 + x)

    See Also
    ========
    Equality

    Notes
    =====
    This class is not the same as the != operator.  The != operator tests
    for exact structural equality between two expressions; this class
    compares expressions mathematically.

    This class is effectively the inverse of Equality.  As such, it uses the
    same algorithms, including any available `_eval_Eq` methods.

    """
    rel_op = '!='

    invert_type = Equality
    is_Unequality = True
    __slots__ = []

    def comprehension(self, operator, *limits, func=None):
        ...

    def abs(self):
        return self.func(abs(self.lhs), abs(self.rhs), given=self)

    def _sympystr(self, p):
        return '%s ≠ %s' % tuple(p._print(arg) for arg in self.args)

    def __new__(cls, lhs, rhs, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)

        evaluate = options.pop('evaluate', global_evaluate[0])

        if evaluate:
            is_equal = Equality(lhs, rhs)
            if isinstance(is_equal, BooleanAtom):
                return is_equal.invert().copy(**options)

        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs != rhs)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return set([self.lhs])
            elif self.rhs.is_Symbol:
                return set([self.rhs])
        return set()

    def _eval_simplify(self, ratio, measure, rational, inverse):
        # simplify as an equality
        eq = Equality(*self.args)._eval_simplify(
            ratio, measure, rational, inverse)
        if isinstance(eq, Equality):
            # send back Ne with the new args
            return self.func(*eq.args)
        return ~eq  # result of Ne is the negated Eq

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            arg = args[0]
            if isinstance(arg, Equality):
                eq = arg
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs)).simplify().overwrite(self, equivalent=[self, eq])
            else:
                return self

        return self

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return Boolean.simplify(self, deep=True, wrt=wrt)

        from sympy.sets.contains import NotSubset
        lhs, rhs = self.args
        if lhs.is_Complement and rhs.is_EmptySet:
            A, B = lhs.args
            return NotSubset(A, B, equivalent=self).simplify()
             
        return super(Unequality, self).simplify()

    def __and__(self, other):
        """Overloading for & operator"""
        if isinstance(other, LessThan):
            if set(self.args) == set(other.args):
                return StrictLessThan(other.lhs, other.rhs, given=[self, other])

        if isinstance(other, GreaterThan):
            if set(self.args) == set(other.args):
                return StrictGreaterThan(other.lhs, other.rhs, given=[self, other])

        if isinstance(other, (StrictLessThan, StrictGreaterThan)):
            if set(self.args) == set(other.args):
                return other

        return Relational.__and__(self, other)

    def asKroneckerDelta(self):
        from sympy.functions.special.tensor_functions import KroneckerDelta
        return 1 - KroneckerDelta(*self.args)

    
Ne = Unequality
Equality.invert_type = Unequality


class _Inequality(Relational):
    """Internal base class for all *Than types.

    Each subclass must implement _eval_relation to provide the method for
    comparing two real numbers.

    """
    __slots__ = []

    def comprehension(self, operator, *limits, func=None):
        from sympy import Integral, Sum
        if operator in (Integral, Sum):
            return Relational.comprehension(self, operator, *limits, func=func)
        return self

    def __new__(cls, lhs, rhs, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)

        evaluate = options.pop('evaluate', global_evaluate[0])

        if evaluate:
            # First we invoke the appropriate inequality method of `lhs`
            # (e.g., `lhs.__lt__`).  That method will try to reduce to
            # boolean or raise an exception.  It may keep calling
            # superclasses until it reaches `Expr` (e.g., `Expr.__lt__`).
            # In some cases, `Expr` will just invoke us again (if neither it
            # nor a subclass was able to reduce to boolean or raise an
            # exception).  In that case, it must call us with
            # `evaluate=False` to prevent infinite recursion.
            r = cls._eval_relation(lhs, rhs)
            if r is not None and r.is_BooleanAtom:
                if 'plausible' in options:
                    if r:
                        del options['plausible']
                    else:
                        options['plausible'] = False

                    return Relational.__new__(cls, lhs, rhs, **options)
                return r.copy(**options)

            # Note: not sure r could be None, perhaps we never take this
            # path?  In principle, could use this to shortcut out if a
            # class realizes the inequality cannot be evaluated further.

        # make a "non-evaluated" Expr for the inequality
        return Relational.__new__(cls, lhs, rhs, **options)


class _Greater(_Inequality):
    """Not intended for general use

    _Greater is only used so that GreaterThan and StrictGreaterThan may
    subclass it for the .gts and .lts properties.

    """
    __slots__ = ()

    def __and__(self, other):
        from sympy.sets.sets import Interval
        from sympy.sets.contains import Contains
        x = None
        if isinstance(other, _Greater):
            if self.lhs == other.rhs:
                x = self.lhs
                
                left = self.rhs
                left_open = isinstance(self, StrictGreaterThan)
                
                right = other.lhs                
                right_open = isinstance(other, StrictGreaterThan)
            elif self.rhs == other.lhs:
                x = self.rhs
                left = other.rhs
                left_open = isinstance(other, StrictGreaterThan)
                
                right = self.lhs
                right_open = isinstance(self, StrictGreaterThan)
            elif self.lhs == other.lhs:
                from sympy import Max
                if self.func == other.func:
                    m = Max(self.rhs, other.rhs)
                    if m is self.rhs:
                        return self
                    if m is other.rhs:
                        return other
                
        elif isinstance(other, _Less):
            if self.rhs == other.rhs:
                x = self.rhs
                left = other.lhs
                left_open = isinstance(other, StrictLessThan)
                
                right = self.lhs
                right_open = isinstance(self, StrictGreaterThan)
            elif self.lhs == other.lhs:
                x = self.lhs
                left = self.rhs
                left_open = isinstance(self, StrictGreaterThan)
                
                right = other.rhs
                right_open = isinstance(other, StrictLessThan)
        if x is not None:                
            return Contains(x, Interval(left, right, left_open=left_open, right_open=right_open, integer=x.is_integer), equivalent=[self, other])
                
        return Relational.__and__(self, other)

    @property
    def gts(self):
        return self._args[0]

    @property
    def lts(self):
        return self._args[1]

    def limit(self, x, xlim, dir='+'):
        """ Compute limit x->xlim.
        """
        return GreaterThan(self.lhs.limit(x, xlim, dir), self.rhs.limit(x, xlim, dir), given=self, evaluate=False)


class _Less(_Inequality):
    """Not intended for general use.

    _Less is only used so that LessThan and StrictLessThan may subclass it for
    the .gts and .lts properties.

    """
    __slots__ = ()

    @property
    def gts(self):
        return self._args[1]

    @property
    def lts(self):
        return self._args[0]

    def __and__(self, other):
        from sympy.sets.sets import Interval
        from sympy.sets.contains import Contains
        x = None
        if isinstance(other, _Greater) :
            if self.rhs == other.rhs:
                x = self.rhs
                
                left = self.lhs 
                left_open = isinstance(self, StrictLessThan)
                
                right = other.lhs 
                right_open = isinstance(other, StrictGreaterThan)
            elif self.lhs == other.lhs:
                x = self.lhs
                
                left = other.rhs
                left_open = isinstance(other, StrictGreaterThan)
                                         
                right = self.rhs
                right_open = isinstance(self, StrictLessThan)
        elif isinstance(other, _Less) :
            if self.rhs == other.lhs:
                x = self.rhs
                
                left = self.lhs
                left_open = isinstance(self, StrictLessThan)
                
                right = other.rhs
                right_open = isinstance(other, StrictLessThan)
            elif self.lhs == other.rhs:
                x = self.lhs
                
                left = other.lhs
                left_open = isinstance(other, StrictLessThan)
                
                right = self.rhs
                right_open = isinstance(self, StrictLessThan)
            elif self.lhs == other.lhs:
                from sympy import Min
                if self.func == other.func:
                    m = Min(self.rhs, other.rhs)
                    if m is self.rhs:
                        return self
                    if m is other.rhs:
                        return other
                        
        if x is not None:                
            return Contains(x, Interval(left, right, left_open=left_open, right_open=right_open, integer=x.is_integer), equivalent=[self, other])
    
        return Relational.__and__(self, other)

    def limit(self, x, xlim, direction='+'):
        """ Compute limit x->xlim.
        """
        return LessThan(self.lhs.limit(x, xlim, direction), self.rhs.limit(x, xlim, direction), given=self, evaluate=False)


class GreaterThan(_Greater):
    """Class representations of inequalities.

    Extended Summary
    ================

    The ``*Than`` classes represent inequal relationships, where the left-hand
    side is generally bigger or smaller than the right-hand side.  For example,
    the GreaterThan class represents an inequal relationship where the
    left-hand side is at least as big as the right side, if not bigger.  In
    mathematical notation:

    lhs >= rhs

    In total, there are four ``*Than`` classes, to represent the four
    inequalities:

    +-----------------+--------+
    |Class Name       | Symbol |
    +=================+========+
    |GreaterThan      | (>=)   |
    +-----------------+--------+
    |LessThan         | (<=)   |
    +-----------------+--------+
    |StrictGreaterThan| (>)    |
    +-----------------+--------+
    |StrictLessThan   | (<)    |
    +-----------------+--------+

    All classes take two arguments, lhs and rhs.

    +----------------------------+-----------------+
    |Signature Example           | Math equivalent |
    +============================+=================+
    |GreaterThan(lhs, rhs)       |   lhs >= rhs    |
    +----------------------------+-----------------+
    |LessThan(lhs, rhs)          |   lhs <= rhs    |
    +----------------------------+-----------------+
    |StrictGreaterThan(lhs, rhs) |   lhs >  rhs    |
    +----------------------------+-----------------+
    |StrictLessThan(lhs, rhs)    |   lhs <  rhs    |
    +----------------------------+-----------------+

    In addition to the normal .lhs and .rhs of Relations, ``*Than`` inequality
    objects also have the .lts and .gts properties, which represent the "less
    than side" and "greater than side" of the operator.  Use of .lts and .gts
    in an algorithm rather than .lhs and .rhs as an assumption of inequality
    direction will make more explicit the intent of a certain section of code,
    and will make it similarly more robust to client code changes:

    >>> from sympy import GreaterThan, StrictGreaterThan
    >>> from sympy import LessThan,    StrictLessThan
    >>> from sympy import And, Ge, Gt, Le, Lt, Rel, S
    >>> from sympy.abc import x, y, z
    >>> from sympy.core.relational import Relational

    >>> e = GreaterThan(x, 1)
    >>> e
    x >= 1
    >>> '%s >= %s is the same as %s <= %s' % (e.gts, e.lts, e.lts, e.gts)
    'x >= 1 is the same as 1 <= x'

    Examples
    ========

    One generally does not instantiate these classes directly, but uses various
    convenience methods:

    >>> for f in [Ge, Gt, Le, Lt]:  # convenience wrappers
    ...     print(f(x, 2))
    x >= 2
    x > 2
    x <= 2
    x < 2

    Another option is to use the Python inequality operators (>=, >, <=, <)
    directly.  Their main advantage over the Ge, Gt, Le, and Lt counterparts,
    is that one can write a more "mathematical looking" statement rather than
    littering the math with oddball function calls.  However there are certain
    (minor) caveats of which to be aware (search for 'gotcha', below).

    >>> x >= 2
    x >= 2
    >>> _ == Ge(x, 2)
    True

    However, it is also perfectly valid to instantiate a ``*Than`` class less
    succinctly and less conveniently:

    >>> Rel(x, 1, ">")
    x > 1
    >>> Relational(x, 1, ">")
    x > 1

    >>> StrictGreaterThan(x, 1)
    x > 1
    >>> GreaterThan(x, 1)
    x >= 1
    >>> LessThan(x, 1)
    x <= 1
    >>> StrictLessThan(x, 1)
    x < 1

    Notes
    =====

    There are a couple of "gotchas" to be aware of when using Python's
    operators.

    The first is that what your write is not always what you get:

        >>> 1 < x
        x > 1

        Due to the order that Python parses a statement, it may
        not immediately find two objects comparable.  When "1 < x"
        is evaluated, Python recognizes that the number 1 is a native
        number and that x is *not*.  Because a native Python number does
        not know how to compare itself with a SymPy object
        Python will try the reflective operation, "x > 1" and that is the
        form that gets evaluated, hence returned.

        If the order of the statement is important (for visual output to
        the console, perhaps), one can work around this annoyance in a
        couple ways:

        (1) "sympify" the literal before comparison

        >>> S(1) < x
        1 < x

        (2) use one of the wrappers or less succinct methods described
        above

        >>> Lt(1, x)
        1 < x
        >>> Relational(1, x, "<")
        1 < x

    The second gotcha involves writing equality tests between relationals
    when one or both sides of the test involve a literal relational:

        >>> e = x < 1; e
        x < 1
        >>> e == e  # neither side is a literal
        True
        >>> e == x < 1  # expecting True, too
        False
        >>> e != x < 1  # expecting False
        x < 1
        >>> x < 1 != x < 1  # expecting False or the same thing as before
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of Relational

        The solution for this case is to wrap literal relationals in
        parentheses:

        >>> e == (x < 1)
        True
        >>> e != (x < 1)
        False
        >>> (x < 1) != (x < 1)
        False

    The third gotcha involves chained inequalities not involving
    '==' or '!='. Occasionally, one may be tempted to write:

        >>> e = x < y < z
        Traceback (most recent call last):
        ...
        TypeError: symbolic boolean expression has no truth value.

        Due to an implementation detail or decision of Python [1]_,
        there is no way for SymPy to create a chained inequality with
        that syntax so one must use And:

        >>> e = And(x < y, y < z)
        >>> type( e )
        And
        >>> e
        (x < y) & (y < z)

        Although this can also be done with the '&' operator, it cannot
        be done with the 'and' operarator:

        >>> (x < y) & (y < z)
        (x < y) & (y < z)
        >>> (x < y) and (y < z)
        Traceback (most recent call last):
        ...
        TypeError: cannot determine truth value of Relational

    .. [1] This implementation detail is that Python provides no reliable
       method to determine that a chained inequality is being built.
       Chained comparison operators are evaluated pairwise, using "and"
       logic (see
       http://docs.python.org/2/reference/expressions.html#notin). This
       is done in an efficient way, so that each object being compared
       is only evaluated once and the comparison can short-circuit. For
       example, ``1 > 2 > 3`` is evaluated by Python as ``(1 > 2) and (2
       > 3)``. The ``and`` operator coerces each side into a bool,
       returning the object itself when it short-circuits. The bool of
       the --Than operators will raise TypeError on purpose, because
       SymPy cannot determine the mathematical ordering of symbolic
       expressions. Thus, if we were to compute ``x > y > z``, with
       ``x``, ``y``, and ``z`` being Symbols, Python converts the
       statement (roughly) into these steps:

        (1) x > y > z
        (2) (x > y) and (y > z)
        (3) (GreaterThanObject) and (y > z)
        (4) (GreaterThanObject.__nonzero__()) and (y > z)
        (5) TypeError

       Because of the "and" added at step 2, the statement gets turned into a
       weak ternary statement, and the first object's __nonzero__ method will
       raise TypeError.  Thus, creating a chained inequality is not possible.

           In Python, there is no way to override the ``and`` operator, or to
           control how it short circuits, so it is impossible to make something
           like ``x > y > z`` work.  There was a PEP to change this,
           :pep:`335`, but it was officially closed in March, 2012.

    """
    __slots__ = ()

    rel_op = '>='

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__ge__(rhs))

    def inverse(self):
        if self.rhs.is_extended_positive:
            if self.lhs.is_extended_positive:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs, equivalent=self)
            from sympy.sets import Contains, Interval
            return Contains(1 / self.lhs, Interval(0, 1 / self.rhs, left_open=True), equivalent=self)
        if self.rhs.is_extended_negative:
            if self.lhs.is_extended_negative:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs, equivalent=self)

        return self

    def subs(self, *args, **kwargs):
        from sympy.simplify import simplify
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
            elif isinstance(eq, StrictLessThan):
                old, new = eq.args
                if eq.plausible:
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)
                return self
            elif isinstance(eq, LessThan):
                old, new = eq.args
                if eq.plausible:
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)

                if self.lhs == eq.lhs and self.rhs == eq.rhs:
                    return Eq(self.lhs, self.rhs, given=[self, eq])

                return self
            elif isinstance(eq, GreaterThan):
                if self.rhs == eq.lhs and self.lhs == eq.rhs:
                    return Eq(self.lhs, self.rhs, given=[self, eq])

                if self.rhs == eq.lhs:
                    return eq.func(self.lhs, eq.rhs, given=[self, eq])
                if self.lhs == eq.rhs:
                    return eq.func(eq.lhs, self.rhs, given=[self, eq])
                return self

            elif isinstance(eq, StrictGreaterThan):
                if self.rhs == eq.lhs:
                    return eq.func(self.lhs, eq.rhs, given=[self, eq])
                if self.lhs == eq.rhs:
                    return eq.func(eq.lhs, self.rhs, given=[self, eq])
                return self
            elif isinstance(eq, Unequality):
                args = eq.args
                lhs = self.lhs.subs(*args, **kwargs)
                rhs = self.rhs.subs(*args, **kwargs)
                if lhs == rhs:
                    return StrictGreaterThan(self.lhs, self.rhs, given=[self, eq])
                return self
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs.subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)

            return self
        old, new = args

        from sympy import Symbol
        if not isinstance(old, Symbol):

            lhs = self.lhs.subs(old, new)
            rhs = self.rhs.subs(old, new)

            g = self.lhs - self.rhs
            _g = lhs - rhs
            if _g < g:
                return StrictLessThan(lhs, rhs, given=self)
            if _g <= g:
                return LessThan(lhs, rhs, given=self)

            if _g > g:
                return GreaterThan(lhs, rhs, given=self)
            if _g >= g:
                return StrictGreaterThan(lhs, rhs, given=self)

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self)
            else:
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))

    def __and__(self, other):
        if isinstance(other, StrictGreaterThan) :
            if self.lhs == other.lhs:
                if other.rhs >= self.rhs:
                    return other
                
        return _Greater.__and__(self, other)


Ge = GreaterThan


class LessThan(_Less):
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

    rel_op = '<='

    def __add__(self, exp):
        exp = sympify(exp)
        if isinstance(exp, (StrictLessThan, LessThan)):
            return exp.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=[self, exp])
        else:
            return Relational.__add__(self, exp)

    def inverse(self):
        if self.rhs.is_extended_positive:
            if self.lhs.is_extended_positive:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs, equivalent=self)
        if self.rhs.is_extended_negative:
            if self.lhs.is_extended_negative:
                return self.reversed_type(1 / self.lhs, 1 / self.rhs, equivalent=self)
            from sympy.sets import Contains, Interval
            return Contains(1 / self.lhs, Interval(1 / self.rhs, 0, right_open=True), equivalent=self)

        return self

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__le__(rhs))

    def subs(self, *args, **kwargs):
        from sympy.simplify import simplify
        from sympy import diff
        from sympy import Symbol        
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
            elif isinstance(eq, StrictLessThan):
                old, new = eq.args
                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs                    
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)

                rhs = self.rhs.subs(old, new)
                if rhs != self.rhs:
                    return eq.func(self.lhs, rhs, given=[self, eq])

                return self
            elif isinstance(eq, LessThan):
                old, new = eq.args

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)

                if self.lhs == eq.rhs and self.rhs == eq.lhs:
                    return Eq(self.lhs, self.rhs, given=[self, eq])

                rhs = self.rhs.subs(old, new).simplify()
                if rhs != self.rhs:
                    return self.func(self.lhs, rhs, given=[self, eq])
                return self
            elif isinstance(eq, GreaterThan):
                old, new = eq.args
                if eq.plausible:
                    return self

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)

                if self.lhs == eq.lhs and self.rhs == eq.rhs:
                    return Eq(self.lhs, self.rhs, given=[self, eq])

                lhs = self.lhs.subs(old, new)
                if lhs != self.lhs:
                    return self.func(lhs, self.rhs, given=[self, eq]).simplify()
                return self
            elif isinstance(eq, StrictGreaterThan):
                old, new = eq.args
                if eq.plausible:
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
#                     _f = lhs - rhs
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)

                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                delta = (lhs - rhs) - (self.lhs - self.rhs)
                match = eq.lhs - eq.rhs

                if delta == match:
                    return eq.func(lhs, rhs, given=[self, eq])
                elif delta == -match:
                    return StrictLessThan(lhs, rhs, given=[self, eq])
                else:
                    return self
            elif isinstance(eq, Unequality):
                args = eq.args
                lhs = self.lhs.subs(*args, **kwargs)
                rhs = self.rhs.subs(*args, **kwargs)
                if lhs == rhs:
                    return StrictLessThan(self.lhs, self.rhs, given=[self, eq])
                return self
            elif isinstance(eq, dict):
                res = self
                for k, v in eq.items():
                    res._subs(k, v)
                return res
            elif eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)

            return self

        if all(isinstance(arg, Relational) for arg in args):
            free_symbols = self.free_symbols
            f = self.lhs - self.rhs
            given = []
            for eq in args:
                if eq.plausible:
                    given.append(eq)
                old, new = eq.args
                if old in free_symbols:
                    domain = old.domain & old.domain_conditioned(eq)
                    if domain != old.domain:
                        _old = Symbol(old.name, domain=domain)
                        f = f.subs(old, _old)
                else:
                    return self

            maxi = f.max()
            if self.plausible:
                return LessThan(maxi, 0, imply=self, given=given)
            return self

        old, new = args
       
        if not isinstance(old, Symbol):
            lhs = self.lhs.subs(old, new)
            rhs = self.rhs.subs(old, new)

            g = self.lhs - self.rhs
            _g = lhs - rhs
            if _g < g:
                return StrictLessThan(lhs, rhs, given=self)
            if _g <= g:
                return LessThan(lhs, rhs, given=self)

            if _g > g:
                return GreaterThan(lhs, rhs, given=self)
            if _g >= g:
                return StrictGreaterThan(lhs, rhs, given=self)

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = self.func(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self)
            else:
                eq = self.func(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))

    def __and__(self, other):
        if isinstance(other, StrictLessThan) :
            if self.lhs == other.lhs:
                if other.rhs <= self.rhs:
                    return other

        return _Less.__and__(self, other)


Le = LessThan


class StrictGreaterThan(_Greater):
    is_StrictGreaterThan = True
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

    rel_op = '>'
    invert_type = LessThan

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__gt__(rhs))

    def __add__(self, exp):
        if isinstance(exp, Equality):
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
        elif isinstance(exp, StrictGreaterThan):
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=[self, exp])

        else:
            return self.func(self.lhs + exp, self.rhs + exp, equivalent=self)

    def subs(self, *args, **kwargs):
        from sympy.simplify import simplify
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
            elif isinstance(eq, (StrictLessThan, LessThan)):
                old, new = eq.args
                if eq.plausible:
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                delta = (lhs - rhs) - (self.lhs - self.rhs)
                match = eq.lhs - eq.rhs

                if delta == match:
                    return eq.func(lhs, rhs, given=[self, eq]).simplify()
                elif delta == -match:
                    return self.func(lhs, rhs, given=[self, eq]).simplify()
                else:
                    return self

                return self
            elif isinstance(eq, GreaterThan):
                old, new = eq.args
                lhs = self.lhs.subs(old, new)
                rhs = self.rhs.subs(old, new)

                delta = (lhs - rhs) - (self.lhs - self.rhs)
                match = eq.lhs - eq.rhs

                if delta == match:
                    return eq.func(lhs, rhs, given=[self, eq]).simplify()
                elif delta == -match:
                    return StrictLessThan(lhs, rhs, given=[self, eq])
                else:
                    return self
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs.subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)

            return self
        old, new = args
        from sympy import Symbol
        old = sympify(old)
        if not isinstance(old, Symbol):
            lhs = self.lhs.subs(old, new)
            rhs = self.rhs.subs(old, new)

            g = self.lhs - self.rhs
            _g = lhs - rhs
            if _g >= g:
                return StrictGreaterThan(lhs, rhs, given=self)
            return self

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self)
            else:
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))
            
    def is_positive_relationship(self):
        if self.rhs.is_zero:
            return self.lhs

    def __and__(self, other):
        if isinstance(other, Unequality) :
            if set(self.args) == set(other.args):
                return self
        elif isinstance(other, Equality) :
            if set(self.args) == set(other.args):
                return S.false.copy(given=[self, other])
        elif isinstance(other, GreaterThan) :
            if self.lhs == other.lhs:
                if self.rhs >= other.rhs:
                    return self
                
        return _Greater.__and__(self, other)

    def __or__(self, other):
        if isinstance(other, Unequality) :
            if set(self.args) == set(other.args):
                return other
        if isinstance(other, Equality) :
            if set(self.args) == set(other.args):
                return GreaterThan(self.lhs, self.rhs, given=[self, other])
            
        return _Greater.__or__(self, other)


Gt = StrictGreaterThan
LessThan.invert_type = StrictGreaterThan


class StrictLessThan(_Less):
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

    is_StrictLessThan = True
    rel_op = '<'
    invert_type = GreaterThan

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        # We don't use the op symbol here: workaround issue #7951
        return _sympify(lhs.__lt__(rhs))

    def __add__(self, exp):
        if isinstance(exp, Equality):
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
        elif isinstance(exp, StrictLessThan):
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=[self, exp])
        else:
            return self.func(self.lhs + exp, self.rhs + exp, equivalent=self)

    def subs(self, *args, **kwargs):
        from sympy.simplify import simplify
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])
            elif isinstance(eq, StrictLessThan):
                old, new = eq.args
                if eq.plausible:
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), equivalent=[self, eq])

                if old in self.free_symbols:
                    f = self.lhs - self.rhs
#                     f = self.lhs - self.rhs > 0
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df > 0:
                        return self
                    elif df < 0:
#                         f > lhs - rhs
#                         f > 0
#                         if we can prove that lhs - rhs>= 0, then we can also prove f > 0
                        return GreaterThan(lhs, rhs, imply=self)
                    else:
                        return self
                    return Eq(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs), imply=self)
                return self
            elif isinstance(eq, dict):
                if eq:
                    subs = self
                    for key, value in eq.items():
                        subs = subs.subs(key, value)
                    return subs
                else:
                    return self
            elif eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)

            return self
        old, new = args
        
        from sympy import Symbol
        if not isinstance(old, Symbol):
            lhs = self.lhs.subs(old, new)
            rhs = self.rhs.subs(old, new)

            g = self.lhs - self.rhs
            _g = lhs - rhs
            if _g < g:
                return StrictLessThan(lhs, rhs, given=self)
            if _g <= g:
                return LessThan(lhs, rhs, given=self)

            if _g > g:
                return GreaterThan(lhs, rhs, given=self)
            if _g >= g:
                return StrictGreaterThan(lhs, rhs, given=self)

        if self.plausible:

            if hasattr(new, 'has') and new.has(old):
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), substituent=self)
            else:
                eq = Eq(self.lhs.subs(old, new), self.rhs.subs(old, new), given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        else:
            return self.func(self.lhs.subs(*args, **kwargs), self.rhs.subs(*args, **kwargs))

    def is_positive_relationship(self):
        if self.lhs.is_zero:
            return self.rhs

    def __and__(self, other):
        if isinstance(other, Unequality) :
            if set(self.args) == set(other.args):
                return self
        elif isinstance(other, Equality) :
            if set(self.args) == set(other.args):
                return S.false.copy(given=[self, other])
        elif isinstance(other, LessThan) :
            if self.lhs == other.lhs:
                if self.rhs <= other.rhs:
                    return self

        return _Less.__and__(self, other)

    def __or__(self, other):
        if isinstance(other, Unequality) :
            if set(self.args) == set(other.args):
                return other
        if isinstance(other, Equality) :
            if set(self.args) == set(other.args):
                return LessThan(self.lhs, self.rhs, given=[self, other])
            
        return _Less.__or__(self, other)


Lt = StrictLessThan
GreaterThan.invert_type = StrictLessThan

Ge.reversed_type = Le
Lt.reversed_type = Gt
Le.reversed_type = Ge
Ne.reversed_type = Ne
Eq.reversed_type = Eq
Gt.reversed_type = Lt

# A class-specific (not object-specific) data item used for a minor speedup.
# It is defined here, rather than directly in the class, because the classes
# that it references have not been defined until now (e.g. StrictLessThan).
Relational.ValidRelationOperator = {
    None: Equality,
    '==': Equality,
    'eq': Equality,
    '!=': Unequality,
    '<>': Unequality,
    'ne': Unequality,
    '>=': GreaterThan,
    'ge': GreaterThan,
    '<=': LessThan,
    'le': LessThan,
    '>': StrictGreaterThan,
    'gt': StrictGreaterThan,
    '<': StrictLessThan,
    'lt': StrictLessThan,
}
