from __future__ import print_function, division

from sympy.core import S
from sympy.core.relational import Eq, Ne, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan, Equality, Unequality
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

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs).simplify(), equivalent=[self, eq]).simplify()
            if isinstance(eq, dict):
                return self
            if eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)
        return BooleanFunction.subs(self, *args, **kwargs)

    def _latex(self, p):
        return r"%s \in %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return r"%s in %s" % tuple(p._print(a) for a in self.args)

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

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    def split(self):
        if self.rhs.is_Union:
            return [self.func(self.lhs, rhs, imply=self) for rhs in self.rhs.args]
        if self.rhs.is_Intersection:
            return [self.func(self.lhs, rhs, given=self) for rhs in self.rhs.args]
        if self.rhs.is_Interval:
            if self.rhs.left_open:
                lower_bound = self.lhs > self.rhs.start
            else:
                lower_bound = self.lhs >= self.rhs.start
            if self.rhs.right_open:
                upper_bound = self.lhs < self.rhs.end
            else:
                upper_bound = self.lhs <= self.rhs.end
            upper_bound.given = lower_bound.given = self
            return [lower_bound, upper_bound]
        return self

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

    def simplify(self, *_, **__):
        e, s = self.args
        if s.is_FiniteSet:
            if len(s) == 1:
                y, *_ = s
                from sympy import Symbol
                if not e._has(Symbol) and y._has(Symbol):
                    return Equality(y, e, equivalent=self)
                return Equality(e, y, equivalent=self)
            return Or(*(Equality(e, y) for y in s), equivalent=self)

        if s.is_ConditionSet:
            if e == s.variable:
                return s.condition.copy(equivalent=self)
            condition = s.condition._subs(s.variable, e)
            condition.equivalent = self
            return condition

        if s.is_Interval and s.is_integer and e.is_Add:
            if not s.left_open or s.right_open:
                try:
                    index = e.args.index(S.NegativeOne)
                    s += S.One
                    e += S.One
                    return self.func(e, s, evaluate=False, equivalent=self)
                except:
                    ...
                    
            if s.left_open or not s.right_open:
                try:
                    index = e.args.index(S.One)
                    s += S.NegativeOne
                    e += S.NegativeOne
                    return self.func(e, s, evaluate=False, equivalent=self)
                except:
                    ...
        
        if s.is_Complement and s.args[1].is_FiniteSet and len(s.args[1]) == 1:
            domain_assumed = e.domain_assumed
            if domain_assumed and domain_assumed == s.args[0]:
                _e, *_ = s.args[1].args
                return Unequality(e, _e, equivalent=self)
            
        return self

# this assertion is useless!
    def assertion(self):
        from sympy.concrete.expr_with_limits import Exists
        e, S = self.args
        x = S.element_symbol(self.free_symbols)
        assert x.dtype == e.dtype
        return Exists(Equality(x, e), (x, S), equivalent=self)

    @property
    def definition(self):
        e, S = self.args

        from sympy.concrete.expr_with_limits import Exists

        condition_set = S.condition_set()
        if condition_set:
            condition = condition_set.condition
            if condition_set.variable != e:
                condition = condition._subs(condition_set.variable, e)
            return And(condition, self.func(e, condition_set.base_set), equivalent=self)

        image_set = S.image_set()
        if image_set is not None:
            expr, variables, base_set = image_set
            from sympy import Wild
            variables_ = Wild(variables.name, **variables.dtype.dict)
            assert variables_.shape == variables.shape
            e = e.subs_limits_with_epitome(expr)
            dic = e.match(expr.subs(variables, variables_))
            if dic:
                variables_ = dic[variables_]
                if variables.dtype != variables_.dtype:
                    assert len(variables.shape) == 1
                    variables_ = variables_[:variables.shape[-1]]
                return Contains(variables_, base_set, equivalent=self)

            if e.has(variables):
                _variables = base_set.element_symbol(e.free_symbols)
                assert _variables.dtype == variables.dtype
                expr = expr._subs(variables, _variables)
                variables = _variables
            assert not e.has(variables)
            return Exists(Equality(e, expr, evaluate=False), (variables, base_set), equivalent=self)

        if S.is_UnionComprehension:
#             from sympy.concrete.expr_with_limits import Exists
            for v in S.variables:
                if self.lhs._has(v):
                    _v = v.generate_free_symbol(self.free_symbols, **v.dtype.dict)
                    S = S.limits_subs(v, _v)

            contains = Contains(self.lhs, S.function).simplify()
            contains.equivalent = None
            return Exists(contains, *S.limits, equivalent=self).simplify()

        return self

    def asSubset(self):
        return Subset(self.lhs.set, self.rhs, equivalent=self)

    def __or__(self, other):
        if other.is_Contains:
            x, X = self.args
            y, Y = other.args
            if x == y:                
                return self.func(x, X | Y, given=[self, other]).simplify()
            
        return BooleanFunction.__or__(self, other)

        
class NotContains(BooleanFunction):
    """
    Asserts that x is not an element of the set S

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
    invert_type = Contains
    is_NotContains = True

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            if isinstance(eq, dict):
                return self
            if eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)

        return self

    def _latex(self, p):
        return r"%s \not\in %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return r"%s not in %s" % tuple(p._print(a) for a in self.args)

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        from sympy.core.sympify import sympify
        if not isinstance(ret, Contains) and (ret in (S.true, S.false) or ret.is_set):
            return sympify(not ret)

#     @property
#     def binary_symbols(self):
#         binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
#         return set().union(*binary_symbols)

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

    def simplify(self, deep=False):
        e, s = self.args
        if s.is_FiniteSet:
            if len(s) == 1:
                y, *_ = s
                return Unequality(e, y, equivalent=self)
            return And(*(Unequality(e, y) for y in s), equivalent=self)

        return self

    @property
    def definition(self):
        e, S = self.args

        from sympy.concrete.expr_with_limits import ForAll

        image_set = S.image_set()
        if image_set is not None:
            expr, variables, base_set = image_set
            from sympy import Wild
            variables_ = Wild(variables.name, **variables.dtype.dict)

            e = e.subs_limits_with_epitome(expr)
            dic = e.match(expr.subs(variables, variables_))
            if dic:
                variables_ = dic[variables_]
                if variables.dtype != variables_.dtype:
                    assert len(variables.shape) == 1
                    variables_ = variables_[:variables.shape[-1]]
                return self.func(variables_, base_set, equivalent=self)

            if e.has(variables):
                _variables = base_set.element_symbol(e.free_symbols)
                assert _variables.dtype == variables.dtype
                expr = expr._subs(variables, _variables)
                variables = _variables
            assert not e.has(variables)
            return ForAll(Unequality(e, expr, evaluate=False), (variables, base_set), equivalent=self)

        condition_set = S.condition_set()
        if condition_set:
            return Or(~condition_set.condition._subs(condition_set.variable, e), ~self.func(e, condition_set.base_set), equivalent=self)

        if S.is_UnionComprehension:
            contains = self.func(self.lhs, S.function).simplify()
            contains.equivalent = None
            return ForAll(contains, *S.limits, equivalent=self).simplify()

        return self

    def __and__(self, other):
        if other.is_Unequality:
            x, X = self.args
            if x == other.rhs:
                X |= {other.lhs}
            elif x == other.lhs:
                X |= {other.rhs}
            else:
                X = None
            if X is not None:
                return self.func(x, X, equivalent=[self, other])      
            
        return BooleanFunction.__and__(self, other)

    def __or__(self, other):
        if other.is_NotContains:
            x, X = self.args
            y, Y = other.args
            if x == y:                
                return self.func(x, X & Y, given=[self, other])
            
        return BooleanFunction.__or__(self, other)

    
Contains.invert_type = NotContains


class Subset(BooleanFunction):
    """
    Asserts that A is a subset of the set S

    """
    is_Subset = True

    def union_comprehension(self, *limits):
        from sympy.concrete.expr_with_limits import UNION
        lhs = UNION(self.lhs, *limits)
        return self.func(lhs, self.rhs, equivalent=self)

    @property
    def reversed(self):
        return Supset(self.rhs, self.lhs, equivalent=self)

    def simplify(self, deep=False):
        from sympy.concrete.expr_with_limits import ForAll
        if self.lhs.is_UnionComprehension:
            return ForAll(self.func(self.lhs.function, self.rhs).simplify(), *self.lhs.limits, equivalent=self).simplify()
        if self.lhs.is_FiniteSet:
            eqs = []
            for e in self.lhs.args:
                eqs.append(Contains(e, self.rhs))
            return And(*eqs, equivalent=self)

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
            return self.func(self.lhs | exp, self.rhs | exp, given=self)

    def intersect(self, exp):
        if isinstance(exp, Subset):
            return self.func(self.lhs & exp.lhs, self.rhs & exp.rhs, given=[self, exp])
        else:
            return self.func(self.lhs & exp, self.rhs & exp, given=self)

    def _latex(self, printer):
        return r'%s \subset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        assert x.is_set and s.is_set, 'expecting Set, not %s' % func_name(s)
        if x.is_Symbol and x.definition is not None:
            x = x.definition
        if s.is_Symbol and s.definition is not None:
            s = s.definition

        if x == s:
            return S.true
        if s.is_Union:
            if x in s._argset:
                return S.true
        if x.is_Intersection:
            for e in x._argset:
                if e in s:
                    return S.true
        if x == S.EmptySet:
            return S.true

        if x.is_ConditionSet and s.is_ConditionSet:
            sym, condition, base_set = x.variable, x.condition, x.base_set
            _sym, _condition, _base_set = s.variable, s.condition, s.base_set
            if sym.dtype == _sym.dtype and (base_set == _base_set or base_set in _base_set):
                if sym != _sym:
                    _condition = _condition._subs(_sym, sym)
                if condition == _condition:
                    return S.true
                if condition.is_And:
                    if _condition.is_And and all(eq in condition._argset for eq in _condition.args) or _condition in condition._argset:
                        return S.true
        if x.is_Piecewise and not s.is_Piecewise:
            return x.func(*((cls(e, s), c) for e, c in x.args))
#         if not x.is_Piecewise and s.is_Piecewise:
#             return s.func(*((cls(x, e), c) for e, c in s.args))
                
#     @property
#     def binary_symbols(self):
#         binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
#         return set().union(*binary_symbols)
# #         return set().union(*[i.binary_symbols
# #             for i in self.args[1].args
# #             if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

    @property
    def definition(self):
        A, B = self.args
        from sympy.concrete.expr_with_limits import ForAll
        e = B.element_symbol(A.free_symbols)
        return ForAll(Contains(e, B), (e, A), equivalent=self).simplify()

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
            elif isinstance(eq, Subset):
                A, B = self.args
                _B, _A = eq.args
                if _B == B:
                    if A == _A: 
                        return Equality(A, B, equivalent=[self, eq])
                    else:
                        return self.func(A, _A, given=[self, eq])
            elif isinstance(eq, Supset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _A == A:
                    return Equality(A, B, equivalent=[self, eq])
            elif eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)

        return self


class NotSubset(BooleanFunction):
    """
    Asserts that A is a subset of the set S

    """
    is_Subset = True
    invert_type = Subset

    @property
    def reversed(self):
        return NotSupset(self.rhs, self.lhs, equivalent=self)

    def simplify(self, deep=False):
        if self.lhs.is_UnionComprehension:
            from sympy.concrete.expr_with_limits import Exists
            return Exists(self.func(self.lhs.function, self.rhs), *self.lhs.limits, equivalent=self)

        if self.lhs.is_FiniteSet and len(self.lhs) == 1:
            return NotContains(self.lhs.arg, self.rhs, equivalent=self).simplify()            
             
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
        return self

    def intersect(self, exp):
        if isinstance(exp, Subset):
            return self.func(self.lhs & exp.lhs, self.rhs & exp.rhs, given=[self, exp])
        else:
            return self.func(self.lhs & exp, self.rhs & exp, given=self)

    def _latex(self, printer):
        return r'%s \not\subset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        assert x.is_set and s.is_set, 'expecting Set, not %s' % func_name(s)
        if x.is_Symbol and x.definition is not None:
            x = x.definition
        if s.is_Symbol and s.definition is not None:
            s = s.definition
        b = cls.invert_type.eval(x, s)
        if b is not None:
            return b.invert()

    @property
    def definition(self):
        A, B = self.args
        from sympy.concrete.expr_with_limits import Exists
        e = B.element_symbol(A.free_symbols)
        return Exists(NotContains(e, B), (e, A), equivalent=self).simplify()

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
            if isinstance(eq, Subset):
                A, B = self.args
                _B, _A = eq.args
                if A == _A and _A == A:
                    return Equality(A, B, equivalent=[self, eq])
            if isinstance(eq, Supset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _A == A:
                    return Equality(A, B, equivalent=[self, eq])

        return self


Subset.invert_type = NotSubset


class Supset(BooleanFunction):
    """
    Asserts that A is a super set of the set S

    """
    is_Supset = True

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            if isinstance(eq, Subset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])
            if isinstance(eq, Supset):
                A, B = self.args
                _B, _A = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])

        return self

    @property
    def reversed(self):
        return Subset(self.rhs, self.lhs, equivalent=self)

    def union_comprehension(self, *limits):
        from sympy.concrete.expr_with_limits import UNION
        rhs = UNION(self.rhs, *limits)
        return self.func(self.lhs, rhs, equivalent=self)

    def simplify(self, deep=False):
        from sympy.concrete.expr_with_limits import ForAll
        if self.rhs.is_UnionComprehension:
            return ForAll(self.func(self.lhs, self.rhs.function).simplify(), *self.rhs.limits, equivalent=self).simplify()
        if self.rhs.is_FiniteSet:
            eqs = []
            for e in self.rhs.args:
                eqs.append(Contains(e, self.lhs))
            return And(*eqs, equivalent=self)
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
        return Subset.eval(s, x)
#     @property
#     def binary_symbols(self):
#         binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
#         return set().union(*binary_symbols)
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
        from sympy.concrete.expr_with_limits import ForAll
        return ForAll(Contains(e, A), (e, B), equivalent=self).simplify()


class NotSupset(BooleanFunction):
    """
    Asserts that A is a super set of the set S

    """
    is_Supset = True
    invert_type = Supset

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equality):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs), equivalent=[self, eq])
            if isinstance(eq, Subset):
                A, B = self.args
                _A, _B = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])
            if isinstance(eq, Supset):
                A, B = self.args
                _B, _A = eq.args
                if A == _A and _B == B:
                    return Equality(A, B, equivalent=[self, eq])

        return self

    @property
    def reversed(self):
        return NotSubset(self.rhs, self.lhs, equivalent=self)

    def simplify(self, deep=False):
        from sympy.concrete.expr_with_limits import Exists
        if self.rhs.is_UnionComprehension:
            return Exists(self.func(self.lhs, self.rhs.function), *self.rhs.limits, equivalent=self).simplify()
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
        return r'%s\not\supset %s' % tuple(printer._print(x) for x in self.args)

    @classmethod
    def eval(cls, x, s):
        return NotSubset.eval(s, x)

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
        from sympy.concrete.expr_with_limits import Exists
        return Exists(NotContains(e, A), (e, B), equivalent=self)


Supset.invert_type = NotSupset

