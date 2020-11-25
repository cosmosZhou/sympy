from typing import Dict, Union, Type
from sympy.utilities.exceptions import SymPyDeprecationWarning
from .add import _unevaluated_Add, Add
from .basic import S, Atom
from .compatibility import ordered
from .basic import Basic
from .evalf import EvalfMixin
from .function import AppliedUndef
from .sympify import _sympify, SympifyError
from .parameters import global_parameters
from sympy.core.logic import fuzzy_bool, fuzzy_xor, fuzzy_and, fuzzy_not
from sympy.logic.boolalg import Boolean, BooleanAtom, And, BinaryCondition
from sympy.core.sympify import sympify, SympifyError
from sympy.core.basic import preorder_traversal

__all__ = (
    'Rel', 'Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge',
    'Relational', 'Equality', 'Unequality', 'StrictLessThan', 'LessThan',
    'StrictGreaterThan', 'GreaterThan',
)

from .expr import Expr
from sympy.multipledispatch import dispatch
from .containers import Tuple
from .symbol import Symbol


def _nontrivBool(side):
    return isinstance(side, Boolean) and \
           not isinstance(side, Atom)

# Note, see issue 4986.  Ideally, we wouldn't want to subclass both Boolean
# and Expr.
# from .. import Expr


def _canonical(cond):
    # return a condition in which all relationals are canonical
    reps = {r: r.canonical for r in cond.atoms(Relational)}
    return cond.xreplace(reps)
    # XXX: AttributeError was being caught here but it wasn't triggered by any of
    # the tests so I've removed it...


# from sympy.logic.boolalg import Boolean
class Relational(BinaryCondition, Expr, EvalfMixin):
    """Base class for all relation types.

    Explanation
    ===========

    Subclasses of Relational should generally be instantiated directly, but
    Relational can be instantiated with a valid ``rop`` value to dispatch to
    the appropriate subclass.

    Parameters
    ==========

    rop : str or None
        Indicates what subclass to instantiate.  Valid values can be found
        in the keys of Relational.ValidRelationOperator.

    Examples
    ========

    >>> from sympy import Rel
    >>> from sympy.abc import x, y
    >>> Rel(y, x + x**2, '==')
    Eq(y, x**2 + x)

    """
    __slots__ = ()

    ValidRelationOperator = {}  # type: Dict[Union[str, None], Type[Relational]]

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
                        if _dic[k].is_boolean:
                            _dic[k] = k.domain_conditioned(_dic[k])
                            
                        if dic[k] not in _dic[k]:
                            return self
                    limits = expr_with_limits.limits_delete(limits, keys)
                    if not limits:
                        continue
                this = f(this, *limits).simplify()

        return this

    def __new__(cls, lhs, rhs, rop=None, **assumptions):

        # If called by a subclass, do nothing special and pass on to Expr.

        if cls is not Relational:
            return BinaryCondition.__new__(cls, lhs, rhs, **assumptions)
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
        >>> -_
        Eq(-x, -1)
        >>> x < 1
        x < 1
        >>> -_
        -x > -1
        """

        lhs, rhs = -self.lhs, -self.rhs
        lhs, rhs = lhs.simplify(), rhs.simplify()
        return self.reversed_type(lhs, rhs, equivalent=self)

    def _eval_evalf(self, prec):
        return self.func(*[s._evalf(prec) for s in self.args])

    @property
    def canonical(self):
        """Return a canonical form of the relational by putting a
        number on the rhs, canonically removing a sign or else
        ordering the args canonically. No other simplification is
        attempted.

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
        >>> (-y < -x).canonical
        x < y
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

    def expand(self, *args, **kwargs):
        return self.func(self.lhs.expand(*args, **kwargs), self.rhs.expand(*args, **kwargs), equivalent=self)

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

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return BinaryCondition.simplify(self, deep=True, wrt=wrt)        

        lhs, rhs = self.args
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
        elif lhs == 0:
            if rhs._coeff_isneg():
                return self.func(-rhs, 0, equivalent=self)
            elif rhs.is_Add:
                _lhs = []
                _rhs = []
                for arg in rhs.args:
                    if arg._coeff_isneg():
                        _lhs.append(-arg)
                    else:
                        _rhs.append(arg)
                if _lhs:
                    return self.func(Add(*_lhs), Add(*_rhs), equivalent=self)            
        elif rhs == 0:
            if lhs._coeff_isneg():
                return self.func(0, -lhs, equivalent=self)
            elif lhs.is_Add:
                _lhs = []
                _rhs = []
                for arg in lhs.args:
                    if arg._coeff_isneg():
                        _rhs.append(-arg)
                    else:
                        _lhs.append(arg)
                if _rhs:
                    return self.func(Add(*_lhs), Add(*_rhs), equivalent=self)
            
        from sympy import Symbol
        if not lhs._has(Symbol) and rhs._has(Symbol):
            return self.reversed
        return self

    def doit(self, *args, **kwargs):
        return self.func(self.lhs.doit(*args, **kwargs), self.rhs.doit(*args, **kwargs), equivalent=self)

    def __add__(self, exp):
        if isinstance(exp, Equality):
            return self.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp]).simplify()
        elif isinstance(exp, Relational):
            return exp.func(self.lhs + exp.lhs, self.rhs + exp.rhs, equivalent=[self, exp])
        elif exp.is_ConditionalBoolean:
            return self.bfn(self.__add__, exp)
        else:
            return self.func(self.lhs + exp, self.rhs + exp, equivalent=self)

    def __sub__(self, exp):
        exp = sympify(exp)
        if exp.is_Equality:
            return self.func(self.lhs - exp.lhs, self.rhs - exp.rhs, equivalent=[self, exp])
        elif exp.is_ConditionalBoolean:
            return self.bfn(self.__sub__, exp)
        else:            
            kwargs = {'given' if exp.is_set else 'equivalent': self}            
            return self.func((self.lhs - exp).simplify(), (self.rhs - exp).simplify(), **kwargs)

    def __mul__(self, exp):
        if isinstance(exp, Equality):
            if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
            return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])
        else:
            if exp.is_extended_positive:
                return self.func(self.lhs * exp, self.rhs * exp, equivalent=self)
            if exp.is_extended_negative:
                return self.reversed_type(self.lhs * exp, self.rhs * exp, equivalent=self)
            elif exp.is_extended_nonnegative:
                return self.func(self.lhs * exp, self.rhs * exp, given=self)
            elif exp.is_extended_nonpositive:
                return self.reversed_type(self.lhs * exp, self.rhs * exp, given=self)
            return self

    def __truediv__(self, exp):
        if isinstance(exp, Equality):
            if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                return self.func(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=[self, exp])
            return self
        else:
            if exp.is_extended_positive:
                return self.func((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self)
            if exp.is_extended_negative:
                return self.reversed_type((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self)
            return self

    def __iter__(self):
        raise TypeError

    def solve(self, x):
        from sympy.sets.contains import Contains
        if not x.is_Symbol:
            _x = self.generate_free_symbol(x.free_symbols, **x.type.dict)
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

    def _latex(self, p):
        if p._settings['itex']:
            gt = r"\gt"
            lt = r"\lt"
        else:
            gt = ">"
            lt = "<"

        charmap = {
            "==": "=",
            ">": gt,
            "<": lt,
            ">=": r"\geq",
            "<=": r"\leq",
            "!=": r"\neq",
        }

        return "%s %s %s" % (p._print(self.lhs), charmap[self.rel_op], p._print(self.rhs))

    def domain_conditioned(self, var):
        from sympy.sets.sets import FiniteSet
        domain = var.domain & self.domain_defined(var)
        from sympy import solve
        equation = self.lhs - self.rhs
        if var.is_integer and not var.is_random:
            from sympy import Dummy
            x = Dummy('x', real=True)
            equation = equation._subs(var, x)
        else:
            x = var
            
        try:
            solution = solve(equation, x)
        except:
            return
            
        if len(solution) == 1:
            solution = solution[0]
            op = type(self)
    
            from sympy import limit
            b = limit(equation, x, S.Infinity)
            a = limit(equation, x, S.NegativeInfinity)
    
            if b.is_extended_negative:
                b = -b
                a = -a
                dic = {Equality: Equality, StrictGreaterThan: StrictLessThan, GreaterThan: LessThan, StrictLessThan: StrictGreaterThan, LessThan: GreaterThan, Unequality: Unequality}
                op = dic[op]
    
            if b.is_extended_positive:
                if a.is_extended_positive:
                    # equation >= 0
                    if op in (LessThan, Equality):  # <=
                        domain &= FiniteSet(solution)
                    elif op == StrictLessThan:
                        domain = solution.emptySet
                    elif op == (StrictGreaterThan, Unequality):  # >
                        domain -= FiniteSet(solution)
                else :
                    from sympy import Interval
                    if op == LessThan:
                        domain &= Interval(S.NegativeInfinity, solution)
                    elif op == GreaterThan:
                        domain &= Interval(solution, S.Infinity)
                    elif op == StrictLessThan:
                        domain &= Interval(S.NegativeInfinity, solution, right_open=True)
                    elif op == StrictGreaterThan:
                        domain &= Interval(solution, S.Infinity, left_open=True)
                    elif op == Unequality:
                        domain -= FiniteSet(solution)
                    elif op == Equality:
                        domain &= FiniteSet(solution)
    
            return domain

    def rewrite(self, *args, **hints):
        return self.func(self.lhs.rewrite(*args, **hints), self.rhs.rewrite(*args, **hints), equivalent=self)

                    
Rel = Relational


class Equal(Relational):
    """An equal relation between two objects.

    Explanation
    ===========

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

    Python treats 1 and True (and 0 and False) as being equal; SymPy
    does not. And integer will always compare as unequal to a Boolean:

    >>> Eq(True, 1), True == 1
    (False, True)

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

    __slots__ = ()

    is_Equality = True

    def __new__(cls, lhs, rhs=None, **options):

        if rhs is None:
            SymPyDeprecationWarning(
                feature="Eq(expr) with rhs default to 0",
                useinstead="Eq(expr, 0)",
                issue=16587,
                deprecated_since_version="1.5"
            ).warn()
            rhs = 0
        evaluate = options.pop('evaluate', global_parameters.evaluate)
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)
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
            elif not (lhs.is_Symbol or rhs.is_Symbol) and (lhs.is_Boolean != rhs.is_Boolean):
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
        """
        return Eq(L, R) as L - R. To control the evaluation of
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
        from .add import _unevaluated_Add, Add
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
                return {self.lhs}
            elif self.rhs.is_Symbol:
                return {self.rhs}
        return set()

    def _eval_simplify(self, **kwargs):
        from .add import Add
        from sympy.solvers.solveset import linear_coeffs
        # standard simplify
        e = super()._eval_simplify(**kwargs)
        if not isinstance(e, Equality):
            return e
        free = self.free_symbols
        if len(free) == 1:
            try:
                x = free.pop()
                m, b = linear_coeffs(
                    e.rewrite(Add, evaluate=False), x)
                if m.is_zero == False:
                    enew = e.func(x, -b / m)
                else:
                    enew = e.func(m * x, -b)
                measure = kwargs['measure']
                if measure(enew) <= kwargs['ratio'] * measure(e):
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
            lhs = (self.lhs / exp).ratsimp().simplify()
            rhs = (self.rhs / exp).ratsimp().simplify()
            if exp.is_nonzero:
                return self.func(lhs, rhs, equivalent=self)
            from sympy import Or
            return Or(self.func(exp, 0), self.func(lhs, rhs), equivalent=self)

    def __mul__(self, exp):
        exp = sympify(exp)
        if isinstance(exp, Equality):
            if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
            return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])

        elif isinstance(exp, StrictLessThan):
            if exp.lhs.is_extended_positive:
                return StrictLessThan(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
            elif exp.lhs.is_extended_nonnegative:
                if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=self)

            elif exp.rhs.is_extended_negative:
                if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                    return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, equivalent=[self, exp])
                return Eq(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])

            elif exp.rhs.is_extended_nonpositive:
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
            if len(lhs.shape) == 2 and det(lhs).is_nonzero:
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
            return self.func(self.lhs & exp, self.rhs & exp, given=self)

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
            return Or(*(self.func(x, x_sol, equivalent=self) for x_sol in res))

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
        new = sympify(new)
        if not old.is_Symbol:
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

            lhs, rhs = self.lhs._subs(old, new), self.rhs._subs(old, new)
            if hasattr(new, 'has') and new.has(old):
                eq = self.func(lhs, rhs, substituent=self)
            else:
                eq = self.func(lhs, rhs, given=self)
            derivative = self.derivative
            if derivative is None:
                derivative = {}
                self.derivative = derivative

            if old not in derivative:
                derivative[old] = {}

            derivative[old][new] = eq
            return eq
        if old.domain_assumed is not None:
            if new in old.domain_assumed:
                ...
            else:
                return self.forall((old,)).subs(old.unbounded, new)

        return self.func(self.lhs.subs(*args, **kwargs).simplify(), self.rhs.subs(*args, **kwargs).simplify())

    def swap(self, x, y):
        if self.plausible:
            return self
        
        from sympy.core.symbol import Dummy
        d = Dummy(**y.type.dict)
        this = self.subs(x, d)
        this = this.subs(y, x)
        return this.subs(d, y)
        
    @staticmethod
    def define(x, expr, given=None):
        from sympy.tensor.indexed import Indexed, Slice
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
            if x is None:                
                return self.func(self.lhs[indices], self.rhs[indices], given=self)
            else:
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
        if self.lhs.is_nonzero or self.rhs.is_nonzero:
            return self.func(log(self.lhs), log(self.rhs), equivalent=self)
        from sympy import Or
        return Or(self.func(self.lhs, 0), self.func(log(self.lhs), log(self.rhs)), equivalent=self)

    def exp(self):
        from sympy import exp
        return self.func(exp(self.lhs).simplify(), exp(self.rhs).simplify(), equivalent=self).simplify()

    def combsimp(self, *args):
        from sympy import combsimp
        return self.func(combsimp(self.lhs, *args), combsimp(self.rhs, *args), equivalent=self)

    def bisect(self, *args, **kwargs):
        if len(args) == 1:
            eq = args[0]
            if not isinstance(eq, slice) and eq.is_boolean:
                from sympy.concrete.expr_with_limits import ForAll
                wrt = kwargs.get('wrt')
                if wrt is None:
                    wrt, *_ = eq.lhs.free_symbols
                if wrt.is_bounded:
                    self = self.forall((wrt,), simplify=False)
                else:
                    self = ForAll(self, (wrt,), equivalent=self)
                assert self.is_ForAll
                return self.bisect(wrt.domain_conditioned(eq))
                                        
        lhs = self.lhs.bisect(*args, **kwargs)
        rhs = self.rhs.bisect(*args, **kwargs)
        if lhs.is_Concatenate and rhs.is_Concatenate:
            return And(*[self.func(lhs, rhs) for lhs, rhs in zip(lhs.args, rhs.args)], equivalent=self)
                
        return self

    def det(self):
        from sympy import det
        return self.func(det(self.lhs), det(self.rhs), given=self)

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return BinaryCondition.simplify(self, deep=True, wrt=wrt)        

        this = self.lhs.func.simplifyEqual(self, *self.args)
        if this is None:
            return self
        return this

    def simplify_Intersection(self, lhs):
        if len(lhs.args) == 2:
            A, B = lhs.args
            if A.is_FiniteSet and B.is_FiniteSet:
                if len(A) == len(B) == 1:
                    return Unequality(A.arg, B.arg, equivalent=self)
        
    def as_two_terms(self):
        return self.func(self.lhs.as_two_terms(), self.rhs.as_two_terms(), equivalent=self).simplify()
    
    def split(self, *args, **kwargs):
        if self.lhs.is_DenseMatrix and self.rhs.is_DenseMatrix:             
            args = [self.func(lhs, rhs, given=self).simplify() for lhs, rhs in zip(self.lhs.args, self.rhs.args)]        
        elif self.lhs.is_FiniteSet:
            from sympy import Contains
            args = [Contains(lhs, self.rhs, given=self).simplify() for lhs in self.lhs.args]                
        else:
            args = None
            
        if args is None:
            return self
            
        if self.plausible:
            self.derivative = args
        return args
        
    def diff(self, *symbols):
        from sympy.core.function import Derivative
        return self.func(Derivative(self.lhs, *symbols), Derivative(self.rhs, *symbols), given=self)

    @property
    def T(self):
        return self.func(self.lhs.T, self.rhs.T, equivalent=self)

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Equal:
            if self.rhs == other.lhs:
                return self.func(self.lhs, other.rhs, equivalent=[self, other])
            elif self.lhs == other.rhs:
                return self.func(other.lhs, self.rhs, equivalent=[self, other])
            elif self.lhs == other.lhs:
                if self.rhs == other.rhs:
                    return self
                return self.func(self.rhs, other.rhs, equivalent=[self, other])
            elif self.rhs == other.rhs:
                return self.func(self.lhs, other.lhs, equivalent=[self, other])
        elif other.is_ConditionalBoolean:
            return self.bfn(self.__and__, other)            
        elif isinstance(other, (StrictLessThan, StrictGreaterThan)):
            if set(self.args) == set(other.args):
                return S.false.copy(given=[self, other])
        return Relational.__and__(self, other)

    def as_KroneckerDelta(self):
        from sympy.functions.special.tensor_functions import KroneckerDelta
        return KroneckerDelta(*self.args)

    def _sympystr(self, p):
        return '%s == %s' % tuple(p._print(arg) for arg in self.args)

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
            kwargs = {'given' if exp.lhs.is_set else 'equivalent': [self, exp]}
            
            return exp.reversed_type((self.lhs - exp.lhs).simplify(), (self.rhs - exp.rhs).simplify(), **kwargs).simplify()
        return Relational.__sub__(self, exp)

    def inverse(self):        
        if self.lhs.shape:
            from sympy.matrices.expressions.determinant import det
            if det(self.lhs).is_nonzero or det(self.rhs).is_nonzero:
                return self.func(self.lhs.inverse(), self.rhs.inverse(), equivalent=self)            
        else:
            if self.lhs.is_nonzero or self.rhs.is_nonzero:
                return self.func(1 / self.lhs, 1 / self.rhs, equivalent=self)
            
        return self

    def simplify_condition_on_random_variable(self):
        lhs, rhs = self.args
        from sympy.stats.rv import pspace
        if lhs.is_symbol and pspace(lhs).symbol == rhs:
            return lhs
        return self             

    def probability(self):
        assert self.lhs.is_random 
        assert self.rhs.is_random
        from sympy.stats.symbolic_probability import Probability
        return self.func(Probability(self.lhs), Probability(self.rhs), equivalent=self)

    def _latex(self, p):
        lhs = self.lhs
        rhs = self.rhs
                    
        if lhs.is_random and lhs.is_symbol:
            from sympy.stats.rv import pspace
            if rhs == pspace(lhs).symbol:
                return p._print(lhs)
            
        elif lhs.is_Probability and rhs.is_Probability:
            lhs = lhs.arg
            rhs = rhs.arg
            
        return "%s = %s" % (p._print(lhs), p._print(rhs))

    def domain_conditioned(self, var):
        if not self.lhs.is_set and not var.is_set:
            return Relational.domain_conditioned(self, var)

    @classmethod
    def rewrite_from_ForAll(cls, self):
        if self.function.is_Equality:
            dic = self.limits_dict
            if len(dic) == 1:
                (x, domain), *_ = dic.items()
                if domain.is_integer and domain.is_Interval:
                    return self.function.reference((x, domain))
        return self
            
    
Eq = Equality = Equal


class Unequal(Relational):
    """An unequal relation between two objects.

    Explanation
    ===========

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
    __slots__ = ()

    def comprehension(self, operator, *limits, func=None):
        ...

    def abs(self):
        return self.func(abs(self.lhs), abs(self.rhs), given=self)

    def _sympystr(self, p):
        return '%s ≠ %s' % tuple(p._print(arg) for arg in self.args)

    def __new__(cls, lhs, rhs, **options):
        lhs = _sympify(lhs)
        rhs = _sympify(rhs)
        evaluate = options.pop('evaluate', global_parameters.evaluate)
        if evaluate:
            is_equal = Equality(lhs, rhs)
            if isinstance(is_equal, BooleanAtom):
                if 'plausible' in options:
                    if is_equal:
                        options['plausible'] = False
                    else:
                        del options['plausible']
                else:
                    return is_equal.invert().copy(**options)

        return Relational.__new__(cls, lhs, rhs, **options)

    @classmethod
    def _eval_relation(cls, lhs, rhs):
        return _sympify(lhs != rhs)

    @property
    def binary_symbols(self):
        if S.true in self.args or S.false in self.args:
            if self.lhs.is_Symbol:
                return {self.lhs}
            elif self.rhs.is_Symbol:
                return {self.rhs}
        return set()

    def _eval_simplify(self, **kwargs):
        # simplify as an equality
        eq = Equality(*self.args)._eval_simplify(**kwargs)
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

        if all(isinstance(arg, Boolean) for arg in args):
            res = self
            for eq in args:
                res = res.subs(eq)
            return res

        old, new = args
        
        if not old.is_Symbol:
            return self

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
        if old.domain_assumed is not None:
            if new in old.domain_assumed:
                ...
            else:
                return self.forall((old,)).subs(old.unbounded, new)
        return self.func(self.lhs.subs(old, new).simplify(), self.rhs.subs(old, new).simplify())

    def simplify(self, deep=False, wrt=None):
        if deep or wrt is not None:
            return BinaryCondition.simplify(self, deep=True, wrt=wrt)

        from sympy.sets.contains import NotSubset
        lhs, rhs = self.args
        if lhs.is_Complement and rhs.is_EmptySet:
            A, B = lhs.args
            return NotSubset(A, B, equivalent=self).simplify()
        
        if lhs.is_KroneckerDelta:
            if rhs.is_zero:
                return Equal(*lhs.args, equivalent=self)
            elif rhs.is_One:
                return self.func(*lhs.args, equivalent=self)
             
        return super(Unequality, self).simplify()

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Or:
            return other.__and__(self)
        if isinstance(other, LessThan):
            if set(self.args) == set(other.args):
                return StrictLessThan(other.lhs, other.rhs, given=[self, other])

        if isinstance(other, GreaterThan):
            if set(self.args) == set(other.args):
                return StrictGreaterThan(other.lhs, other.rhs, given=[self, other])

        if isinstance(other, (StrictLessThan, StrictGreaterThan)):
            if set(self.args) == set(other.args):
                return other

        if isinstance(other, Equality):
            argset = {*self.args}
            _argset = {*other.args}
            x = argset & _argset
            if len(x) == 2:
                return S.false.copy(equivalent=[self, other])
            elif len(x) == 1:
                x, *_ = x
                argset.remove(x)
                _argset.remove(x)
                lhs, *_ = argset
                rhs, *_ = _argset
                eq = Equality(lhs, rhs).simplify()
                if eq.is_BooleanFalse:                    
                    return other
                
        return Relational.__and__(self, other)

    def __truediv__(self, exp):
        if exp.is_Equality:
            if exp.lhs.is_nonzero or exp.rhs.is_nonzero:
                return self.func(self.lhs / exp.lhs, self.rhs / exp.rhs, equivalent=[self, exp])
            return self
        else:
            if exp.is_nonzero:
                return self.func((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp(), equivalent=self)
            if exp.is_zero:
                return self
            from sympy import Or 
            return Or(Equal(exp, 0), self.func((self.lhs / exp).ratsimp(), (self.rhs / exp).ratsimp()), equivalent=self)

    def as_KroneckerDelta(self):
        from sympy.functions.special.tensor_functions import KroneckerDelta
        return 1 - KroneckerDelta(*self.args)

    def __mul__(self, exp):
        if isinstance(exp, Unequal):
            return self.func(self.lhs * exp.lhs, self.rhs * exp.rhs, given=[self, exp])
        
        return Relational.__mul__(self, exp)

    def domain_conditioned(self, var):
        if not self.lhs.is_set:            
            return Relational.domain_conditioned(self, var)


Ne = Unequality = Unequal
Equality.invert_type = Unequality


class Inequality(Relational):
    """Internal base class for all *Than types.

    Each subclass must implement _eval_relation to provide the method for
    comparing two real numbers.

    """
    __slots__ = ()

    def comprehension(self, operator, *limits, func=None):
        from sympy import Integral, Sum
        if operator in (Integral, Sum):
            return Relational.comprehension(self, operator, *limits, func=func)
        return self

    def __new__(cls, lhs, rhs, **options):

        try:
            lhs = _sympify(lhs)
            rhs = _sympify(rhs)
        except SympifyError:
            return NotImplemented

        evaluate = options.pop('evaluate', global_parameters.evaluate)
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

    @classmethod
    def _eval_relation(cls, lhs, rhs, **options):
        val = cls._eval_fuzzy_relation(lhs, rhs)
        if val is None:
            return cls(lhs, rhs, evaluate=False)
        else:
            return _sympify(val)


class _Greater(Inequality):
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


class _Less(Inequality):
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
            return Contains(x, Interval(left, right, left_open=left_open, right_open=right_open, integer=x.is_integer), equivalent=[self, other]).simplify()
    
        return Relational.__and__(self, other)

    def limit(self, x, xlim, direction='+'):
        """ Compute limit x->xlim.
        """
        return LessThan(self.lhs.limit(x, xlim, direction), self.rhs.limit(x, xlim, direction), given=self, evaluate=False)


class GreaterThan(_Greater):
    """Class representations of inequalities.

    Explanation
    ===========

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
        (4) (GreaterThanObject.__bool__()) and (y > z)
        (5) TypeError

       Because of the "and" added at step 2, the statement gets turned into a
       weak ternary statement, and the first object's __bool__ method will
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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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
        elif isinstance(other, Unequal):
            if self.lhs == other.lhs:
                if other.rhs == self.rhs:
                    return StrictGreaterThan(self.lhs, self.rhs, equivalent=[self, other])            
                
        return _Greater.__and__(self, other)


Ge = GreaterThan


class LessThan(_Less):
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

    rel_op = '<='

    def __add__(self, exp):
        exp = sympify(exp)
        if isinstance(exp, (StrictLessThan, LessThan)):
            return exp.func(self.lhs + exp.lhs, self.rhs + exp.rhs, given=[self, exp]).simplify()
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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs                    
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
#                     _f = lhs - rhs
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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
        from sympy import Interval
        if other.is_StrictLessThan:
            if self.lhs == other.lhs:
                if other.rhs <= self.rhs:
                    return other
        if other.is_Contains:
            if self.lhs == other.lhs:
                if other.rhs.is_Interval:
                    return other.func(self.lhs, Interval(S.NegativeInfinity, self.rhs, integer=other.rhs.is_integer) & other.rhs).simplify()
                
        return _Less.__and__(self, other)


Le = LessThan


class StrictGreaterThan(_Greater):
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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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

    def as_KroneckerDelta(self):
        from sympy import KroneckerDelta
        lhs, rhs = self.args        
        if lhs.is_Symbol:
            domain = lhs.domain_assumed
            if domain and domain.is_Interval:
                if rhs == domain.min():
                    return 1 - KroneckerDelta(lhs, rhs)
        if rhs.is_Symbol:
            domain = rhs.domain_assumed
            if domain and domain.is_Interval:
                if domain.max() == lhs:
                    return 1 - KroneckerDelta(lhs, rhs)            


Gt = StrictGreaterThan
LessThan.invert_type = StrictGreaterThan


class StrictLessThan(_Less):
    __doc__ = GreaterThan.__doc__
    __slots__ = ()

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
#                     f = self.lhs - self.rhs.is_extended_positive
                    lhs = simplify(self.lhs.subs(old, new))
                    rhs = simplify(self.rhs.subs(old, new))
                    _f = lhs - rhs
                    from sympy import diff
                    df = diff(f, old)
                    if df.is_extended_positive:
                        return self
                    elif df.is_extended_negative:
#                         f > lhs - rhs
#                         f.is_extended_positive
#                         if we can prove that lhs - rhs>= 0, then we can also prove f.is_extended_positive
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

    def as_KroneckerDelta(self):
        from sympy import KroneckerDelta
        lhs, rhs = self.args        
        if lhs.is_Symbol:
            domain = lhs.domain_assumed
            if domain and domain.is_Interval:
                if domain.max() == rhs:
                    return 1 - KroneckerDelta(lhs, rhs)
        if rhs.is_Symbol:
            domain = rhs.domain_assumed
            if domain and domain.is_Interval:
                if lhs == domain.min():
                    return 1 - KroneckerDelta(lhs, rhs)


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


def _n2(a, b):
    """Return (a - b).evalf(2) if a and b are comparable, else None.
    This should only be used when a and b are already sympified.
    """
    # /!\ it is very important (see issue 8245) not to
    # use a re-evaluated number in the calculation of dif
    if a.is_comparable and b.is_comparable:
        dif = (a - b).evalf(2)
        if dif.is_comparable:
            return dif


@dispatch(Expr, Expr)
def _eval_is_ge(lhs, rhs):
    return None


@dispatch(Basic, Basic)
def _eval_is_eq(lhs, rhs):
    return None


@dispatch(Tuple, Expr)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return False


@dispatch(Tuple, AppliedUndef)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return None


@dispatch(Tuple, Symbol)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    return None


@dispatch(Tuple, Tuple)  # type: ignore
def _eval_is_eq(lhs, rhs):  # noqa:F811
    if len(lhs) != len(rhs):
        return False

    return fuzzy_and(fuzzy_bool(is_eq(s, o)) for s, o in zip(lhs, rhs))


def is_lt(lhs, rhs):
    """Fuzzy bool for lhs is strictly less than rhs.

    See the docstring for is_ge for more
    """
    return fuzzy_not(is_ge(lhs, rhs))


def is_gt(lhs, rhs):
    """Fuzzy bool for lhs is strictly greater than rhs.

    See the docstring for is_ge for more
    """
    return fuzzy_not(is_le(lhs, rhs))


def is_le(lhs, rhs):
    """Fuzzy bool for lhs is less than or equal to rhs.
    is_gt calls is_lt
    See the docstring for is_ge for more
    """
    return is_ge(rhs, lhs)


def is_ge(lhs, rhs):
    """
    Fuzzy bool for lhs is greater than or equal to rhs.

    Parameters
    ==========

    lhs: Expr
        The left-hand side of the expression, must be sympified,
        and an instance of expression. Throws an exception if
        lhs is not an instance of expression.

    rhs: Expr
        The right-hand side of the expression, must be sympified
        and an instance of expression. Throws an exception if
        lhs is not an instance of expression.

    Returns
    =======

    Expr : True if lhs is greater than or equal to rhs, false is
        lhs is less than rhs, and None if the comparison between
        lhs and rhs is indeterminate.

    The four comparison functions ``is_le``, ``is_lt``, ``is_ge``, and ``is_gt`` are
    each implemented in terms of ``is_ge`` in the following way:

    is_ge(x, y) := is_ge(x, y)
    is_le(x, y) := is_ge(y, x)
    is_lt(x, y) := fuzzy_not(is_ge(x, y))
    is_gt(x, y) = fuzzy_not(is_ge(y, x))

    To maintain these equivalences in fuzzy logic it is important that in cases where
    either x or y is non-real all comparisons will give None.

    InEquality classes, such as Lt, Gt, etc. Use one of is_ge, is_le, etc.
    To implement comparisons with ``Gt(a, b)`` or ``a > b`` etc for an ``Expr`` subclass
    it is only necessary to define a dispatcher method for ``_eval_is_ge`` like

    >>> from sympy.core.relational import is_ge, is_lt, is_gt
    >>> from sympy.abc import x
    >>> from sympy import S, Expr, sympify
    >>> from sympy.multipledispatch import dispatch
    >>> class MyExpr(Expr):
    ...     def __new__(cls, arg):
    ...         return Expr.__new__(cls, sympify(arg))
    ...     @property
    ...     def value(self):
    ...         return self.args[0]
    ...
    >>> @dispatch(MyExpr, MyExpr)
    ... def _eval_is_ge(a, b):
    ...     return is_ge(a.value, b.value)
    ...
    >>> a = MyExpr(1)
    >>> b = MyExpr(2)
    >>> a < b
    True
    >>> a <= b
    True
    >>> a > b
    False
    >>> is_lt(a, b)
    True

    Examples
    ========


    >>> is_ge(S(2), S(0))
    True
    >>> is_ge(S(0), S(2))
    False
    >>> is_ge(S(0), x)

    >>> is_gt(S(2), S(0))
    True
    >>> is_gt(S(0), S(2))
    False
    >>> is_lt(S(0), S(2))
    True
    >>> is_lt(S(2), S(0))
    False

   """
    if not (isinstance(lhs, Expr) and isinstance(rhs, Expr)):
        raise TypeError("Can only compare inequalities with Expr")

    retval = _eval_is_ge(lhs, rhs)

    if retval is not None:
        return retval
    else:
        n2 = _n2(lhs, rhs)
        if n2 is not None:
            # use float comparison for infinity.
            # otherwise get stuck in infinite recursion
            if n2 in (S.Infinity, S.NegativeInfinity):
                n2 = float(n2)
            return _sympify(n2 >= 0)
        if lhs.is_extended_real and rhs.is_extended_real:
            if (lhs.is_infinite and lhs.is_extended_positive) or (rhs.is_infinite and rhs.is_extended_negative):
                return True
            diff = lhs - rhs
            if diff is not S.NaN:
                rv = diff.is_extended_nonnegative
                if rv is not None:
                    return rv


def is_neq(lhs, rhs):
    """Fuzzy bool for lhs does not equal rhs.

    See the docstring for is_eq for more
    """
    return fuzzy_not(is_eq(lhs, rhs))


def is_eq(lhs, rhs):
    """
    Fuzzy bool representing mathematical equality between lhs and rhs.

    Parameters
    ==========

    lhs: Expr
        The left-hand side of the expression, must be sympified.

    rhs: Expr
        The right-hand side of the expression, must be sympified.

    Returns
    =======

    True if lhs is equal to rhs, false is lhs is not equal to rhs, and
    None if the comparison between lhs and rhs is indeterminate.

    Explanation
    ===========

    This function is intended to give a relatively fast determination and deliberately does not attempt slow
    calculations that might help in obtaining a determination of True or False in more difficult cases.

    InEquality classes, such as Lt, Gt, etc. Use one of is_ge, is_le, etc.
    To implement comparisons with ``Gt(a, b)`` or ``a > b`` etc for an ``Expr`` subclass
    it is only necessary to define a dispatcher method for ``_eval_is_ge`` like

    >>> from sympy.core.relational import is_eq
    >>> from sympy.core.relational import is_neq
    >>> from sympy import S, Basic, Eq, sympify
    >>> from sympy.abc import x
    >>> from sympy.multipledispatch import dispatch
    >>> class MyBasic(Basic):
    ...     def __new__(cls, arg):
    ...         return Basic.__new__(cls, sympify(arg))
    ...     @property
    ...     def value(self):
    ...         return self.args[0]
    ...
    >>> @dispatch(MyBasic, MyBasic)
    ... def _eval_is_eq(a, b):
    ...     return is_eq(a.value, b.value)
    ...
    >>> a = MyBasic(1)
    >>> b = MyBasic(1)
    >>> a == b
    True
    >>> Eq(a, b)
    True
    >>> a != b
    False
    >>> is_eq(a, b)
    True


    Examples
    ========



    >>> is_eq(S(0), S(0))
    True
    >>> Eq(0, 0)
    True
    >>> is_neq(S(0), S(0))
    False
    >>> is_eq(S(0), S(2))
    False
    >>> Eq(0, 2)
    False
    >>> is_neq(S(0), S(2))
    True
    >>> is_eq(S(0), x)

    >>> Eq(S(0), x)
    Eq(0, x)



    """
    from sympy.core.add import Add
    from sympy.functions.elementary.complexes import arg
    from sympy.simplify.simplify import clear_coefficients
    from sympy.utilities.iterables import sift

    # here, _eval_Eq is only called for backwards compatibility
    # new code should use is_eq with multiple dispatch as
    # outlined in the docstring
    for side1, side2 in (lhs, rhs), (rhs, lhs):
        eval_func = getattr(side1, '_eval_Eq', None)
        if eval_func is not None:
            retval = eval_func(side2)
            if retval is not None:
                return retval

    retval = _eval_is_eq(lhs, rhs)
    if retval is not None:
        return retval

    if dispatch(type(lhs), type(rhs)) != dispatch(type(rhs), type(lhs)):
        retval = _eval_is_eq(rhs, lhs)
        if retval is not None:
            return retval

    # retval is still None, so go through the equality logic
    # If expressions have the same structure, they must be equal.
    if lhs == rhs:
        return True  # e.g. True == True
    elif all(isinstance(i, BooleanAtom) for i in (rhs, lhs)):
        return False  # True != False
    elif not (lhs.is_Symbol or rhs.is_Symbol) and (
        isinstance(lhs, Boolean) != 
        isinstance(rhs, Boolean)):
        return False  # only Booleans can equal Booleans

    if lhs.is_infinite or rhs.is_infinite:
        if fuzzy_xor([lhs.is_infinite, rhs.is_infinite]):
            return False
        if fuzzy_xor([lhs.is_extended_real, rhs.is_extended_real]):
            return False
        if fuzzy_and([lhs.is_extended_real, rhs.is_extended_real]):
            return fuzzy_xor([lhs.is_extended_positive, fuzzy_not(rhs.is_extended_positive)])

        # Try to split real/imaginary parts and equate them
        I = S.ImaginaryUnit

        def split_real_imag(expr):
            real_imag = lambda t: (
                'real' if t.is_extended_real else
                'imag' if (I * t).is_extended_real else None)
            return sift(Add.make_args(expr), real_imag)

        lhs_ri = split_real_imag(lhs)
        if not lhs_ri[None]:
            rhs_ri = split_real_imag(rhs)
            if not rhs_ri[None]:
                eq_real = Eq(Add(*lhs_ri['real']), Add(*rhs_ri['real']))
                eq_imag = Eq(I * Add(*lhs_ri['imag']), I * Add(*rhs_ri['imag']))
                return fuzzy_and(map(fuzzy_bool, [eq_real, eq_imag]))

        # Compare e.g. zoo with 1+I*oo by comparing args
        arglhs = arg(lhs)
        argrhs = arg(rhs)
        # Guard against Eq(nan, nan) -> Falsesymp
        if not (arglhs == S.NaN and argrhs == S.NaN):
            return fuzzy_bool(Eq(arglhs, argrhs))

    if all(isinstance(i, Expr) for i in (lhs, rhs)):
        # see if the difference evaluates
        dif = lhs - rhs
        z = dif.is_zero
        if z is not None:
            if z is False and dif.is_commutative:  # issue 10728
                return False
            if z:
                return True

        n2 = _n2(lhs, rhs)
        if n2 is not None:
            return _sympify(n2 == 0)

        # see if the ratio evaluates
        n, d = dif.as_numer_denom()
        rv = None
        if n.is_zero:
            rv = d.is_nonzero
        elif n.is_finite:
            if d.is_infinite:
                rv = True
            elif n.is_zero is False:
                rv = d.is_infinite
                if rv is None:
                    # if the condition that makes the denominator
                    # infinite does not make the original expression
                    # True then False can be returned
                    l, r = clear_coefficients(d, S.Infinity)
                    args = [_.subs(l, r) for _ in (lhs, rhs)]
                    if args != [lhs, rhs]:
                        rv = fuzzy_bool(Eq(*args))
                        if rv is True:
                            rv = None
        elif any(a.is_infinite for a in Add.make_args(n)):
            # (inf or nan)/x != 0
            rv = False
        if rv is not None:
            return rv
