from __future__ import print_function, division

from sympy.core import S
from sympy.core.relational import Eq, Ne, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan, Equality
from sympy.logic.boolalg import BooleanFunction, And, Or
from sympy.utilities.misc import func_name




class Contains(BooleanFunction):
    """
    Asserts that x is an element of the set S

    Examples
    ========

    >>> from sympy import Symbol, Integer, S
    >>> from sympy.sets.contains import Contains
    >>> Contains(Integer(2), S.Integers)
    True
    >>> Contains(Integer(-2), S.Naturals)
    False
    >>> i = Symbol('i', integer=True)
    >>> Contains(i, S.Naturals)
    Contains(i, Naturals)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Element_%28mathematics%29
    """
    is_Contains = True

    def _latex(self, p):
        return r"%s \in %s" % tuple(p._print(a) for a in self.args)

    @property
    def negated(self):
        return NotContains(*self.args, counterpart=self)

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if not isinstance(ret, Contains) and (ret in (S.true, S.false) or ret.is_set):
            return ret

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)
#         return set().union(*[i.binary_symbols
#             for i in self.args[1].args
#             if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    def split(self):
        if not self.rhs.is_Union:
            return self
        return Or(*(self.func(self.lhs, rhs) for rhs in self.rhs.args), equivalent=self)

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def as_two_terms(self):
        from sympy.sets.sets import Interval

        if not isinstance(self.set, Interval):
            return self

        res = [None] * 2

        kwargs = self.clauses()
        kwargs['given'] = self if self.plausible else None
        kwargs['evaluate'] = False

        if self.set.left_open:
            res[0] = StrictGreaterThan(self.element, self.set.start, **kwargs)
        else:
            res[0] = GreaterThan(self.element, self.set.start, **kwargs)

        if self.set.right_open:
            res[1] = StrictLessThan(self.element, self.set.end, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.end, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    def simplifier(self):
        e, s = self.args
        if s.is_FiniteSet:
            if len(s) == 1:
                y, *_ = s
                return Equality(e, y, equivalent=self)
            return Or(*(Equality(e, y) for y in s), equivalent=self)

        return self

    @property
    def definition(self):
        e, S = self.args
        from sympy.sets.conditionset import image_set_definition
        assertion = image_set_definition(S)

        if assertion is not None:
            for k, *v in assertion.limits:
                if len(v) == 1 and v[0] == S:
                    b = k
                    break

            assertion = assertion.function
            
            assertion = assertion._subs(b, e)

            assertion.equivalent = self
            return assertion
        if S.is_ConditionSet:
            return And(S.condition._subs(S.sym, e), self.func(e, S.base_set), equivalent=self)

        if S.is_UnionComprehension:
            from sympy.sets.sets import Interval
            exists = {}
            for limit in S.limits:
                x, *args = limit
                if len(limit) == 2:
                    exists[x] = args[0]
                elif len(limit) == 3:
                    exists[x] = Interval(*args, integer=True)
                else:
                    exists[x] = None
            return Contains(self.lhs, S.function, exists=self.combine_exists(exists), forall=self.forall, equivalent=self).simplifier()

        return self


class NotContains(BooleanFunction):
    """
    Asserts that x is an element of the set S

    Examples
    ========

    >>> from sympy import Symbol, Integer, S
    >>> from sympy.sets.contains import Contains
    >>> Contains(Integer(2), S.Integers)
    True
    >>> Contains(Integer(-2), S.Naturals)
    False
    >>> i = Symbol('i', integer=True)
    >>> Contains(i, S.Naturals)
    Contains(i, Naturals)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Element_%28mathematics%29
    """

    @property
    def negated(self):
        return Contains(*self.args, exists=self.forall, forall=self.exists, counterpart=self)

    def _latex(self, p):
        return r"%s \notin %s" % tuple(p._print(a) for a in self.args)

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if not isinstance(ret, Contains) and (ret in (S.true, S.false) or ret.is_set):
            return not ret

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def simplifier(self):
        forall = self.forall
        if forall is not None:
            if len(forall) == 1 and isinstance(forall, dict):
                (e, s), *_ = forall.items()
                image_set = s.image_set()
                if image_set is not None:
                    expr, sym, base_set = image_set
                    element = base_set.element_symbol(expr.free_symbols | s.free_symbols | sym.free_symbols)
                    assert element.dtype == base_set.element_type

                    _e, S = self.args
                    return self.func(_e.subs(e, expr.subs(sym, element)), S, forall={element : base_set}, equivalent=self)

        return self

    @property
    def definition(self):
        e, S = self.args
        from sympy.core.symbol import Symbol
        if isinstance(S, Symbol):
            assertion = S.assertion()

            for k, v in assertion.forall.items():
                if v == S:
                    b = k
                    break

            del assertion.forall[b]
            assertion = assertion._subs(b, e)

            assertion.forall = assertion.combine_clause(assertion.forall, self.forall)
            assertion.exists = assertion.combine_clause(assertion.exists, self.exists)
            assertion.equivalent = self
            return assertion

        return self


class Subset(BooleanFunction):
    """
    Asserts that A is a subset of the set S

    """

    @property
    def reversed(self):
        return Supset(self.rhs, self.lhs, equivalent=self)

    def simplifier(self):
        from sympy.sets.sets import Interval
        if self.lhs.is_UnionComprehension:
            forall = {}
            for limit in self.lhs.limits:
                x, *args = limit
                if len(limit) == 3:
                    forall[x] = Interval(*args, integer=True)
                elif len(limit) == 2:
                    forall[x] = args[0]
                else:
                    forall[x] = None

            return self.func(self.lhs.function, self.rhs, forall=self.combine_clause(self.forall, forall), exists=self.exists, equivalent=self)

        return self

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    def union(self, exp):
        if isinstance(exp, Subset):
            return self.func(self.lhs | exp.lhs, self.rhs | exp.rhs, given=[self, exp])
        else:
            return Eq(self.lhs | exp, self.rhs | exp, given=self)

    def _latex(self, printer):
        return r'%s \subset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
#         from sympy.sets.sets import Set

        assert x.is_set and s.is_set, 'expecting Set, not %s' % func_name(s)
        if x == s:
            return S.true

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)
#         return set().union(*[i.binary_symbols
#             for i in self.args[1].args
#             if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    @property
    def definition(self):
        A, B = self.args
        from sympy.concrete.expr_with_limits import Forall
        e = B.element_symbol(A.free_symbols)
        return Forall(Contains(e, B), (e, A), equivalent=self)

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def as_two_terms(self):
        from sympy.sets.sets import Interval

        if not isinstance(self.set, Interval):
            return self

        res = [None] * 2

        kwargs = self.clauses()
        kwargs['given'] = self if self.plausible else None
        kwargs['evaluate'] = False

        if self.set.left_open:
            res[0] = StrictGreaterThan(self.element, self.set.start, **kwargs)
        else:
            res[0] = GreaterThan(self.element, self.set.start, **kwargs)

        if self.set.right_open:
            res[1] = StrictLessThan(self.element, self.set.end, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.end, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])

        return self


class Supset(BooleanFunction):
    """
    Asserts that A is a super set of the set S

    """

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])

        return self

    @property
    def reversed(self):
        return Subset(self.rhs, self.lhs, equivalent=self)

    def simplifier(self):
        from sympy.concrete.expr_with_limits import Forall
        if self.rhs.is_UnionComprehension:
            return Forall(self.func(self.lhs, self.rhs.function), *self.rhs.limits, equivalent=self).simplifier()
        return self

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    def _latex(self, printer):
        return r'%s\supset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        from sympy.sets.sets import Set

        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)
#         return set().union(*[i.binary_symbols
#             for i in self.args[1].args
#             if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def as_two_terms(self):
        from sympy.sets.sets import Interval

        if not isinstance(self.set, Interval):
            return self

        res = [None] * 2

        kwargs = self.clauses()
        kwargs['given'] = self if self.plausible else None
        kwargs['evaluate'] = False

        if self.set.left_open:
            res[0] = StrictGreaterThan(self.element, self.set.start, **kwargs)
        else:
            res[0] = GreaterThan(self.element, self.set.start, **kwargs)

        if self.set.right_open:
            res[1] = StrictLessThan(self.element, self.set.end, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.end, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos(), equivalent=self)

    @property
    def definition(self):
        A, B = self.args
        e = A.element_symbol(B.free_symbols)
        from sympy.concrete.expr_with_limits import Forall
        return Forall(Contains(e, A), (e, B), equivalent=self)

