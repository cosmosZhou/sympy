from sympy.core import S
from sympy.core.relational import Eq, Ne, Less, Greater, \
    LessEqual, GreaterEqual, Equal, Unequal
from sympy.logic.boolalg import And, Or, BinaryCondition


class Contains(BinaryCondition):
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
                result = self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs))
            
                return self.subs_assumptions_for_equality(eq, result)
            if isinstance(eq, dict):
                return self
            if eq.is_ConditionalBoolean:
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
            from sympy.utilities.miscellany import func_name
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if ret is None or not isinstance(ret, Contains) and (ret in (S.true, S.false) or ret.is_set):
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
        from sympy.sets.sets import Interval

        if not isinstance(self.set, Interval):
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
        this = s.func.simplify_Contains(self, e, s)
        if this is not None:
            return this
        return self

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_NotContains:
            if self.element == other.element:
                from sympy import Complement
                s = Complement(self.set, other.set)
                return self.func(self.element, s)
        elif other.is_Contains:
            if self.element == other.element:
                s = self.set & other.set
                return self.func(self.element, s)
        elif self.rhs.is_Interval:
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
        if other.is_Contains:
            print('this should be axiomatized!!!!')
            x, X = self.args
            y, Y = other.args
            if x == y: 
                return self.func(x, X | Y, given=[self, other]).simplify()
            
        elif other.is_Or:            
            return other.func(self, *other.args)
        
        return BinaryCondition.__or__(self, other)

    def __truediv__(self, other):
        if other.is_nonzero:
            e, s = self.args
            return self.func(e / other, s / other, given=self)
            
        return self

    def as_KroneckerDelta(self):
        x, domain = self.args 
        if domain.is_FiniteSet:
            return domain.as_KroneckerDelta(x)
    
        domain = x.domain - domain
        if domain.is_FiniteSet: 
            return 1 - domain.as_KroneckerDelta(x)
            
    def inverse(self):
        rhs = self.rhs.inverse()
        if rhs is not None:
            return self.func(1 / self.lhs, rhs)
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
        if interval.is_Interval: 
            poly = self.lhs.as_poly(x)
            if poly is not None and poly.degree() == 1:
                c1 = poly.nth(1)
                c0 = poly.nth(0)
                if interval.is_integer:
                    if c1 == 1:
                        interval = interval.copy(start=interval.start - c0, stop=interval.stop - c0)
                        return domain & interval
                    elif c1 == -1:
                        interval = interval.copy(start=c0 - interval.stop, stop=c0 - interval.start, left_open=interval.right_open, right_open=interval.left_open)
                        return domain & interval                            
                else:
                    if c1 > 0:
                        interval.func(start=(interval.start - c0) / c1, stop=(interval.stop - c0) / c1)
                        return domain & interval
                    elif c1 < 0:
                        interval.func(start=(interval.stop - c0) / c1, stop=(interval.start - c0) / c1, left_open=interval.right_open, right_open=interval.left_open)
                        return domain & interval             
      
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


class NotContains(BinaryCondition):
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
            if eq.is_ConditionalBoolean:
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
            from sympy.utilities.miscellany import func_name
            raise TypeError('expecting Set, not %s' % func_name(s))

        ret = s.contains(x)
        if ret is None:
            return
        if not isinstance(ret, Contains) and (ret in (S.true, S.false) or ret.is_set):
            from sympy.core.sympify import sympify
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
        this = s.func.simplify_NotContains(self, e, s)
        if this is not None:
            return this
            
        domain = e.domain // s
        if domain.is_FiniteSet:
            return self.invert_type(e, domain).simplify()
        
        return self

    def __and__(self, other):
        if other.is_NotContains:
            if self.element == other.element:
                s = self.set | other.set
                return self.func(self.element, s)
        elif other.is_Contains:
            if self.element == other.element:
                from sympy import Complement
                s = Complement(other.set, self.set)
                return other.func(self.element, s)
        
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
                if interval.is_Interval:
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
        if other.is_NotContains:
            x, X = self.args
            y, Y = other.args
            if x == y: 
                return self.func(x, X & Y, given=[self, other])
            
        return BinaryCondition.__or__(self, other)

    def as_KroneckerDelta(self):
        x, domain = self.args 
        if domain.is_FiniteSet:
            return 1 - domain.as_KroneckerDelta(x)
        domain = x.domain - domain
        if domain.is_FiniteSet:
            return domain.as_KroneckerDelta(x)
            
    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs.T, self.rhs)

    def domain_conditioned(self, x): 
        if self.lhs == x:
            domain = x.domain & self.domain_defined(x)
            return x.domain_conditioned(self.invert_type(x, domain // self.rhs))
        
    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        element, container = function.args
        forall = self.limits_dict
        if element in forall:
            if forall[element] == container:
                return S.BooleanFalse

        
Contains.invert_type = NotContains
