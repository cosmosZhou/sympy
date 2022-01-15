from sympy.core import S
from sympy.core.relational import Eq, Ne, Less, Greater, \
    LessEqual, GreaterEqual, Equal, Unequal
from sympy.logic.boolalg import And, Or, BinaryCondition
from sympy.utilities.misc import func_name
from sympy.core.sympify import _sympify, sympify


class Subset(BinaryCondition):
    """
    Asserts that A is a subset of the set S

    """

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def simplify(self, deep=False):
        if self.lhs.is_FiniteSet:
            eqs = []
            for e in self.lhs.args:
                from sympy import Element                
                eqs.append(Element(e, self.rhs))
            return And(*eqs)

        return self

    def _sympystr(self, p):
#                 \N{SUBSET OF}
        return '%s \N{SUBSET OF OR EQUAL TO} %s' % tuple(p._print(x) for x in self.args)
    
    def _latex(self, printer):
        return r'%s \subset %s' % tuple(printer._print(x) for x in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{SUBSET OF OR EQUAL TO} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

    @classmethod
    def eval(cls, lhs, rhs):
        assert lhs.is_set and rhs.is_set, 'expecting Set, not %s' % func_name(rhs)
        if lhs.is_symbol and lhs.definition is not None:
            lhs = lhs.definition
        if rhs.is_symbol and rhs.definition is not None:
            rhs = rhs.definition

        if lhs == rhs:
            return S.true
        ret = rhs._eval_Subset_reversed(lhs)
        if ret is not None:
            return ret

        ret = lhs._eval_Subset(rhs)
        if ret is not None:
            return ret        
                
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

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                result = self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs))
                return self.subs_assumptions_for_equality(eq, result)                
            elif eq.is_Quantifier:
                return self.bfn(self.subs, eq)
            return self

        return BinaryCondition.subs(self, *args, **kwargs)

    def __and__(self, other):
        if other.is_Supset:
            if self.args == other.args:
                # apply squeeze theorem
                return Equal(*self.args)
        elif other.is_Subset:
            lhs, rhs = self.args
            if (rhs, lhs) == other.args:
                # apply squeeze theorem
                return Equal(*self.args)
            elif rhs == other.rhs:
                return self.func(lhs | other.lhs, rhs)
            elif lhs == other.lhs:
                return self.func(lhs, rhs & other.rhs)
            
        return BinaryCondition.__and__(self, other)

    def domain_conditioned(self, x):
        if self.lhs.is_FiniteSet:
            if x.type in self.lhs.etype:
                if x in self.lhs:
                    from sympy import Element
                    return Element(x, self.rhs).domain_conditioned(x)
                
        return BinaryCondition.domain_conditioned(self, x)

    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        if function.lhs.is_FiniteSet:
            function, S = function.lhs, function.rhs
            res = self.simplify_int_limits(function)
            if res:
                function, limits = res            
                function = Subset(function, S).simplify()
                return self.func(function, *limits).simplify()


class NotSubset(BinaryCondition):
    """
    Asserts that A is a subset of the set S

    """
    invert_type = Subset

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return BinaryCondition.eval(cls, *args, **assumptions)

    def simplify(self, deep=False):
        if self.lhs.is_Cup:
            from sympy import Any
            return Any(self.func(self.lhs.expr, self.rhs), *self.lhs.limits)

        if self.lhs.is_FiniteSet and len(self.lhs) == 1:
            from sympy import NotElement
            return NotElement(self.lhs.arg, self.rhs).simplify()            
             
        return self

    def _sympystr(self, p):
        #  NEITHER A SUBSET OF NOR EQUAL TO      
#         \N{SUBSET OF WITH NOT EQUAL TO}
        return '%s \N{NOT A SUBSET OF} %s' % tuple(p._print(x) for x in self.args)

    def _latex(self, printer):
        return r'%s \not\subset %s' % tuple(printer._print(x) for x in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{NOT A SUBSET OF} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

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

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if isinstance(eq, Equal):
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs))

        return self


Subset.invert_type = NotSubset


class Supset(BinaryCondition):
    """
    Asserts that A is a super set of the set S

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
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs))
            return self
        return BinaryCondition.subs(self, *args, **kwargs)
    
    def __and__(self, other):
        if other.is_Subset:
            if self.args == other.args:
                # apply squeeze theorem
                return Equal(*self.args)
        elif other.is_Supset:
            lhs, rhs = self.args
            if (rhs, lhs) == other.args:
                # apply squeeze theorem
                return Equal(*self.args)
            elif lhs == other.lhs: 
                return self.func(lhs, rhs | other.rhs)
            elif rhs == other.rhs: 
                return self.func(lhs & other.lhs, rhs)
            
        return BinaryCondition.__and__(self, other)
    
    def simplify(self, deep=False):
        if self.rhs.is_FiniteSet:
            eqs = []
            for e in self.rhs.args:
                from sympy import Element                
                eqs.append(Element(e, self.lhs))
            return And(*eqs)
        return self

    def _sympystr(self, p):
#         \N{SUPERSET OF}
        return '%s \N{SUPERSET OF OR EQUAL TO} %s' % tuple(p._print(x) for x in self.args)

    def _latex(self, printer):
        return r'%s\supset %s' % tuple(printer._print(x) for x in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{SUPERSET OF OR EQUAL TO} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

    @classmethod
    def eval(cls, x, s):
        return Subset.eval(s, x)

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


class NotSupset(BinaryCondition):
    """
    Asserts that A is a super set of the set S

    """
    invert_type = Supset

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
                return self.func(self.lhs._subs(*args, **kwargs), self.rhs._subs(*args, **kwargs))
        return self

    def simplify(self, deep=False):
        from sympy import Any
        if self.rhs.is_Cup:
            return Any(self.func(self.lhs, self.rhs.expr), *self.rhs.limits).simplify()
        return self

    def _sympystr(self, p):
#  NEITHER A SUPERSET OF NOR EQUAL TO
#         \N{SUPERSET OF WITH NOT EQUAL TO}
        return '%s \N{NOT A SUPERSET OF} %s' % tuple(p._print(x) for x in self.args)

    def _latex(self, printer):
        return r'%s\not\supset %s' % tuple(printer._print(x) for x in self.args)

    def _pretty(self, p):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict
        from sympy.printing.str import sstr
        
        var, s = self.args
        if p._use_unicode:
            el = u" \N{NOT A SUPERSET OF} "
            return prettyForm(*stringPict.next(p._print(var),
                                               el, p._print(s)), binding=8)
        else:
            return prettyForm(sstr(self))

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


Supset.invert_type = NotSupset

Supset.reversed_type = Subset
Subset.reversed_type = Supset
NotSubset.reversed_type = NotSupset
NotSupset.reversed_type = NotSubset

