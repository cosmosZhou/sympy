from sympy.core import S
from sympy.core.relational import Eq, Ne, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan, Equality, Unequality
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
            if isinstance(eq, Equality):
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
        return r"%s ∈ %s" % tuple(p._print(a) for a in self.args)

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

    def split(self, *args, **kwargs):
        if self.rhs.is_Union:
            args = [self.func(self.lhs, rhs, imply=self) for rhs in self.rhs.args]
#             if self.plausible:
#                 self.derivative = args
            return args
        if self.rhs.is_Intersection:
            args = [self.func(self.lhs, rhs, given=self) for rhs in self.rhs.args]
            if self.plausible:
                self.derivative = args
            return args
        
        if self.rhs.is_Interval:
            if self.rhs.left_open:
                lower_bound = self.lhs > self.rhs.start
            else:
                lower_bound = self.lhs >= self.rhs.start
            if self.rhs.right_open:
                upper_bound = self.lhs < self.rhs.stop
            else:
                upper_bound = self.lhs <= self.rhs.stop
            upper_bound.given = lower_bound.given = self
            args = [lower_bound, upper_bound]
            if self.plausible:
                self.derivative = args
            return args
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
            res[1] = StrictLessThan(self.element, self.set.stop, **kwargs)
        else:
            res[1] = LessThan(self.element, self.set.stop, **kwargs)
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
        this = s.func.simplify_Contains(self, e, s)
        if this is not None:
            return this
        return self

# this assertion is useless!
    def assertion(self):
        from sympy import Exists
        e, S = self.args
        x = S.element_symbol(self.free_symbols)
        assert x.type == e.type
        return Exists(Equality(x, e), (x, S), equivalent=self)

    @property
    def definition(self):
        print("Contains.definition should be axiomatized!")
        
        e, S = self.args

        from sympy import Exists

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
            variables_ = Wild(variables.name, **variables.type.dict)
            assert variables_.shape == variables.shape
            e = e.subs_limits_with_epitome(expr)
            dic = e.match(expr.subs(variables, variables_))
            if dic:
                variables_ = dic[variables_]
                if variables.type != variables_.type:
                    assert len(variables.shape) == 1
                    variables_ = variables_[:variables.shape[-1]]
                return Contains(variables_, base_set, equivalent=self)

            if e._has(variables):
                _variables = base_set.element_symbol(e.free_symbols)
                assert _variables.type == variables.type
                expr = expr._subs(variables, _variables)
                variables = _variables
            assert not e._has(variables)
            return Exists(Equality(e, expr, evaluate=False), (variables, base_set), equivalent=self)

        return self

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_NotContains:
            if self.element == other.element:
                from sympy import Complement
                s = Complement(self.set, other.set)
                return self.func(self.element, s, equivalent=[self, other])
        elif other.is_Contains:
            if self.element == other.element:
                s = self.set & other.set
                return self.func(self.element, s, equivalent=[self, other])
            elif self.rhs == other.rhs:
                from sympy import Subset                
                return Subset(self.lhs.set | other.lhs.set, self.rhs, equivalent=[self, other])
            
        return BinaryCondition.__and__(self, other)

    def __or__(self, other):
        if other.is_Contains:
            x, X = self.args
            y, Y = other.args
            if x == y:                
                return self.func(x, X | Y, given=[self, other]).simplify()
            
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
            return self.func(1 / self.lhs, rhs, equivalent=self)
        return self

    @property
    def T(self):
        assert len(self.lhs.shape) <= 1
        return self.func(self.lhs.T, self.rhs, equivalent=self)
      
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
                        return S.BooleanTrue.copy(equivalent=self)


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
            if isinstance(eq, Equality):
                args = eq.args
                result = self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs))
                return self.subs_assumptions_for_equality(eq, result)
            if isinstance(eq, dict):
                return self
            if eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)
            return self

        return BinaryCondition.subs(self, *args, **kwargs) 

    def _latex(self, p):
        return r"%s \not\in %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return r"%s ∉ %s" % tuple(p._print(a) for a in self.args)

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
            
        domain = e.domain - s
        if domain.is_FiniteSet:
            return self.invert_type(e, domain).simplify()
        
        return self

    @property
    def definition(self):
        print("NotContains.definition should be axiomatized!")
        e, S = self.args

        from sympy import ForAll

        image_set = S.image_set()
        if image_set is not None:
            expr, variables, base_set = image_set
            from sympy import Wild
            variables_ = Wild(variables.name, **variables.type.dict)

            e = e.subs_limits_with_epitome(expr)
            dic = e.match(expr.subs(variables, variables_))
            if dic:
                variables_ = dic[variables_]
                if variables.type != variables_.type:
                    assert len(variables.shape) == 1
                    variables_ = variables_[:variables.shape[-1]]
                return self.func(variables_, base_set, equivalent=self)

            if e.has(variables):
                _variables = base_set.element_symbol(e.free_symbols)
                assert _variables.type == variables.type
                expr = expr._subs(variables, _variables)
                variables = _variables
            assert not e.has(variables)
            return ForAll(Unequality(e, expr, evaluate=False), (variables, base_set), equivalent=self)

        condition_set = S.condition_set()
        if condition_set:
            return Or(~condition_set.condition._subs(condition_set.variable, e), ~self.func(e, condition_set.base_set), equivalent=self)

        return self

    def __and__(self, other):
        if other.is_NotContains:
            if self.element == other.element:
                s = self.set | other.set
                return self.func(self.element, s, equivalent=[self, other])
        elif other.is_Contains:
            if self.element == other.element:
                from sympy import Complement
                s = Complement(other.set, self.set)
                return other.func(self.element, s, equivalent=[self, other])
        
        elif other.is_Unequality:
            x, X = self.args
            if x == other.rhs:
                X |= {other.lhs}
            elif x == other.lhs:
                X |= {other.rhs}
            else:
                X = None
            if X is not None:
                return self.func(x, X, equivalent=[self, other])      
            
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
        return self.func(self.lhs.T, self.rhs, equivalent=self)

    def split(self, *args, **kwargs):
        if self.rhs.is_Union:
            args = [self.func(self.lhs, rhs, given=self) for rhs in self.rhs.args]
            if self.plausible:
                self.derivative = args
            return args
        if self.rhs.is_Intersection:
            return [self.func(self.lhs, rhs, imply=self) for rhs in self.rhs.args]
        
        if self.rhs.is_Interval:
            if self.rhs.left_open:
                lower_bound = self.lhs <= self.rhs.start
            else:
                lower_bound = self.lhs < self.rhs.start
            if self.rhs.right_open:
                upper_bound = self.lhs >= self.rhs.stop
            else:
                upper_bound = self.lhs > self.rhs.stop
            upper_bound.imply = lower_bound.imply = self
            return [lower_bound, upper_bound]
        return self

    def domain_conditioned(self, x):        
        if self.lhs == x:
            domain = x.domain & self.domain_defined(x)
            return x.domain_conditioned(self.invert_type(x, domain - self.rhs))
        
    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        element, container = function.args
        forall = self.limits_dict
        if element in forall:
            if forall[element] == container:
                return S.BooleanFalse.copy(equivalent=self)

        
Contains.invert_type = NotContains
