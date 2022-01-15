from sympy.core import S
from sympy.core.relational import Eq, Ne, Less, Greater, \
    LessEqual, GreaterEqual, Equal
from sympy.logic.boolalg import BinaryCondition
from sympy.core.sympify import sympify


class Element(BinaryCondition):
    """
    Asserts that x is an element of the set S

    Examples
    ========

    >>> from sympy import Symbol, Integer, S
    >>> from sympy.sets.contains import Element
    >>> Element(Integer(2), S.Integers)
    True
    >>> Element(Integer(-2), S.Naturals)
    False
    >>> i = Symbol('i', integer=True)
    >>> Element(i, S.Naturals)
    Element(i, Naturals)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Element_%28mathematics%29
    """

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def subs(self, *args, **kwargs):
        [*args] = map(sympify, args)
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                result = self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs))
            
                return self.subs_assumptions_for_equality(eq, result)
            if isinstance(eq, dict):
                return self
            if eq.is_Quantifier:
                return self.bfn(self.subs, eq)
            return self
        
        return BinaryCondition.subs(self, *args, **kwargs)

    def _latex(self, p):
        return r"%s \in %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return "%s \N{ELEMENT OF} %s" % tuple(p._print(a) for a in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{ELEMENT OF} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            from sympy.utilities.misc import func_name
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if ret is None or not isinstance(ret, Element) and (ret in (S.true, S.false) or ret.is_set):
            return ret

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)

    def as_set(self):
        return self

    @property
    def set(self):
        return self.args[1]

    @property
    def element(self):
        return self.args[0]

    def as_two_terms(self):
        if not self.set.is_Interval:
            return self

        res = [None] * 2

        kwargs = self.clauses()
        kwargs['given'] = self if self.plausible else None
        kwargs['evaluate'] = False

        if self.set.left_open:
            res[0] = Greater(self.element, self.set.start, **kwargs)
        else:
            res[0] = GreaterEqual(self.element, self.set.start, **kwargs)

        if self.set.right_open:
            res[1] = Less(self.element, self.set.stop, **kwargs)
        else:
            res[1] = LessEqual(self.element, self.set.stop, **kwargs)
        return res

    def cos(self):
        x, s = self.args
        from sympy import cos
        return self.func(cos(x), s.cos(), given=self)

    def acos(self):
        x, s = self.args
        from sympy import acos
        return self.func(acos(x), s.acos())

    def simplify(self, *_, **__):
        e, s = self.args
        this = s.func.simplify_Element(self, e, s)
        if this is not None:
            return this
        return self

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_NotElement:
            if self.element == other.element:
                return self.func(self.element, self.rhs - other.rhs).simplify()
        elif other.is_Element:
            if self.element == other.element:
                s = self.rhs & other.rhs
                return self.func(self.element, s)
        elif self.rhs.is_Range or self.rhs.is_Interval:
            if other.is_LessEqual: 
                if self.lhs == other.lhs:
                    if self.rhs.left_open:
                        if other.rhs <= self.rhs.start:
                            return S.false
                    else: 
                        if other.rhs < self.rhs.start:
                            return S.false
            elif other.is_Less:
                if self.lhs == other.lhs:
                    if other.rhs <= self.rhs.start:
                        return S.false
            elif other.is_GreaterEqual:
                if self.lhs == other.lhs:
                    if self.rhs.right_open:
                        if other.rhs >= self.rhs.stop:
                            return S.false
                    else: 
                        if other.rhs > self.rhs.stop:
                            return S.false
            elif other.is_Greater:
                if self.lhs == other.lhs:
                    if other.rhs >= self.rhs.stop:
                        return S.false
            
        return BinaryCondition.__and__(self, other)

    def __or__(self, other):
        if other.is_Element:
            x, X = self.args
            y, Y = other.args
            if x == y: 
                return self.func(x, X | Y).simplify()
            
        elif other.is_Or: 
            return other.func(self, *other.args)
        
        return BinaryCondition.__or__(self, other)

    def __truediv__(self, other):
        if other.is_nonzero:
            e, s = self.args
            return self.func(e / other, s / other)
            
        return self

    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs.T, self.rhs)
      
    def domain_conditioned(self, x):
        domain = x.domain & self.domain_defined(x)
        if x == self.lhs:
            return self.rhs
        interval = self.rhs
        if interval.is_Range: 
            poly = self.lhs.as_poly(x)
            if poly is not None and poly.degree() == 1:
                c1 = poly.nth(1)
                c0 = poly.nth(0)
                if c1 == 1:
                    interval = interval.func(interval.start - c0, interval.stop - c0, interval.step, **interval.kwargs)
                    return domain & interval
                elif c1 == -1:
                    interval = interval.func(c0 - interval.stop, c0 - interval.start, interval.step, left_open=interval.right_open, right_open=interval.left_open)
                    return domain & interval                            
      
        elif interval.is_Interval: 
            poly = self.lhs.as_poly(x)
            if poly is not None and poly.degree() == 1:
                c1 = poly.nth(1)
                c0 = poly.nth(0)
                if c1 > 0:
                    interval.func(start=(interval.start - c0) / c1, stop=(interval.stop - c0) / c1)
                    return domain & interval
                elif c1 < 0:
                    interval.func(start=(interval.stop - c0) / c1, stop=(interval.start - c0) / c1, left_open=interval.right_open, right_open=interval.left_open)
                    return domain & interval
                
        return BinaryCondition.domain_conditioned(self, x)
                                 
    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        x = function.lhs
        limits_dict = self.limits_dict
        if x in limits_dict:
            domain = limits_dict[x]
            if not isinstance(domain, list):
                if domain.is_set:
                    if domain in function.rhs:
                        return S.BooleanTrue


class NotElement(BinaryCondition):
    """
    Asserts that x is not an element of the set S

    Examples
    ========

    >>> from sympy import Symbol, Integer, S
    >>> from sympy.sets.contains import Element
    >>> Element(Integer(2), S.Integers)
    True
    >>> Element(Integer(-2), S.Naturals)
    False
    >>> i = Symbol('i', integer=True)
    >>> Element(i, S.Naturals)
    Element(i, Naturals)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Element_%28mathematics%29
    """
    invert_type = Element

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                result = self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs))
                return self.subs_assumptions_for_equality(eq, result)
            if isinstance(eq, dict): 
                for k, v in eq.items():
                    self = self._subs(k, v)
                return self
            if eq.is_Quantifier:
                return self.bfn(self.subs, eq)
            return self

        return BinaryCondition.subs(self, *args, **kwargs) 

    def _latex(self, p):
        return r"%s \not\in %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return "%s \N{NOT AN ELEMENT OF} %s" % tuple(p._print(a) for a in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{NOT AN ELEMENT OF} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            from sympy.utilities.misc import func_name
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if ret is None:
            return
        if not isinstance(ret, Element) and (ret in (S.true, S.false) or ret.is_set):
            return sympify(not ret)

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
        this = s.func.simplify_NotElement(self, e, s)
        if this is not None:
            return this
            
        domain = e.domain - s
        if domain.is_FiniteSet:
            return self.invert_type(e, domain).simplify()
        
        return self

    def __and__(self, other):
        if other.is_NotElement:
            if self.element == other.element:
                s = self.rhs | other.rhs
                return self.func(self.element, s)
        elif other.is_Element:
            if self.element == other.element:
                return other.func(self.element, other.set - self.set)
        
        elif other.is_Unequal:
            x, X = self.args
            if x == other.rhs:
                X |= {other.lhs}
            elif x == other.lhs:
                X |= {other.rhs}
            else:
                X = None
            if X is not None:
                return self.func(x, X)
        elif other.is_GreaterEqual: 
            if self.lhs == other.lhs:
                interval = self.rhs
                if interval.is_Range:
                    if interval.start == other.rhs:
                        return other.func(other.lhs, interval.stop)
                elif interval.is_Interval:
                    if interval.left_open:
                        if interval.right_open:
                            ...
                        else:
                            ...
                    else:
                        if interval.right_open:
                            if interval.start == other.rhs:
                                return other.func(other.lhs, interval.stop)
                        else:
                            ...
            
        return BinaryCondition.__and__(self, other)

    def __or__(self, other):
        if other.is_NotElement:
            x, X = self.args
            y, Y = other.args
            if x == y: 
                return self.func(x, X & Y, given=[self, other])
            
        return BinaryCondition.__or__(self, other)

    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs.T, self.rhs)

    def domain_conditioned(self, x): 
        if self.lhs == x:
            domain = x.domain & self.domain_defined(x)
            return x.domain_conditioned(self.invert_type(x, domain - self.rhs))
        return BinaryCondition.domain_conditioned(self, x)
        
    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        element, container = function.args
        forall = self.limits_dict
        if element in forall:
            if forall[element] == container:
                return S.BooleanFalse


class Contains(BinaryCondition):
    """
    Asserts that x is an element of the set S

    Examples
    ========

    >>> from sympy import Symbol, Integer, S
    >>> from sympy.sets.contains import Element
    >>> Contains(S.Integers, Integer(2))
    True
    >>> Contains(S.Naturals, Integer(-2))
    False
    >>> i = Symbol('i', integer=True)
    >>> Contains(S.Naturals, i)
    Contains(Naturals, i)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Element_%28mathematics%29
    """

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def _latex(self, p):
        return r"%s \ni %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        # unicodedata.lookup('CONTAINS AS MEMBER'), '\N{CONTAINS AS MEMBER}'
        return "%s \N{CONTAINS AS MEMBER} %s" % tuple(p._print(a) for a in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{CONTAINS AS MEMBER} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

    @classmethod
    def eval(cls, s, x):
        if not s.is_set:
            from sympy.utilities.misc import func_name
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if ret is None or not isinstance(ret, Element) and (ret in (S.true, S.false) or ret.is_set):
            return ret

    @property
    def binary_symbols(self):
        binary_symbols = [i.binary_symbols for i in self.args[1].args if hasattr(i, 'binary_symbols') and (i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne)))]
        return set().union(*binary_symbols)

    def as_set(self):
        return self

    def simplify(self, *_, **__):
        return self

    def __and__(self, other):
        """Overloading for & operator"""
        return BinaryCondition.__and__(self, other)

    def __or__(self, other):
        return BinaryCondition.__or__(self, other)

    def __truediv__(self, other):
        if other.is_nonzero:
            s, e = self.args
            return self.func(s / other, e / other)
            
        return self

    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs, self.rhs.T)
      
    def domain_conditioned(self, x):
        return BinaryCondition.domain_conditioned(self, x)


class NotContains(BinaryCondition):
    """
    Asserts that x is not an element of the set S

    Examples
    ========

    >>> from sympy import Symbol, Integer, S
    >>> from sympy.sets.contains import Element
    >>> Element(Integer(2), S.Integers)
    True
    >>> Element(Integer(-2), S.Naturals)
    False
    >>> i = Symbol('i', integer=True)
    >>> Element(i, S.Naturals)
    Element(i, Naturals)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Element_%28mathematics%29
    """
    invert_type = Contains

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def _latex(self, p):
        return r"%s \not\ni %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return "%s \N{DOES NOT CONTAIN AS MEMBER} %s" % tuple(p._print(a) for a in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{DOES NOT CONTAIN AS MEMBER} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

    @classmethod
    def eval(cls, x, s):
        if not s.is_set:
            from sympy.utilities.misc import func_name
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if ret is None:
            return
        if not isinstance(ret, Element) and (ret in (S.true, S.false) or ret.is_set):
            return sympify(not ret)

    def as_set(self):
        return self

    def simplify(self, *_, **__):
        return self

    def __and__(self, other):
        return BinaryCondition.__and__(self, other)

    def __or__(self, other):
        return BinaryCondition.__or__(self, other)

    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs, self.rhs.T)

    def domain_conditioned(self, x): 
        return BinaryCondition.domain_conditioned(self, x)
        
        
Contains.invert_type = NotContains
Element.invert_type = NotElement

Element.reversed_type = Contains
NotElement.reversed_type = NotContains
Contains.reversed_type = Element
NotContains.reversed_type = NotElement
