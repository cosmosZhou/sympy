from sympy.logic.boolalg import Boolean, BooleanTrue
from sympy.concrete.expr_with_limits import ExprWithLimits
from sympy.core.sympify import sympify
from sympy.utilities.iterables import postorder_traversal


class ConditionalBoolean(Boolean, ExprWithLimits):
    """A boolean object is an object for which logic operations make sense."""
    
    __slots__ = []

    _op_priority = 12.1  # higher than Relational

    # this will change the default new operator!
    def __new__(cls, function, *symbols, **assumptions):
        if function.is_BooleanAtom or len(symbols) == 0:
            return function.copy(**assumptions)
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def __getitem__(self, rhs):
        return self.this.function.__getitem__(rhs)

    def __mul__(self, rhs):
        return self.this.function.__mul__(rhs)
        
    def __mod__(self, rhs):
        return self.this.function.__mod__(rhs)
    
    def __truediv__(self, rhs):
        return self.this.function.__truediv__(rhs)

    def __matmul__(self, rhs):
        return self.this.function.__matmul__(rhs)
    
    def __rmatmul__(self, rhs):
        return self.this.function.__rmatmul__(rhs)
    
    @property
    def T(self):
        return self.this.function.T
    
    def inverse(self):
        return self.this.function.inverse()

    @staticmethod
    def merge_func(funcs, _funcs):
        array = []
        i = len(funcs) - 1
        j = len(_funcs) - 1
        while i >= 0 and j >= 0:
            func, limits = funcs[i]
            _func, _limits = _funcs[j]
            if func.is_Exists:
                if _func.is_ForAll:
                    array.append(funcs[i])
                else:
                    array.append((func, limits + _limits))
                    j -= 1
                i -= 1
            else:
                if _func.is_ForAll:
                    array.append(funcs[i])
                    array.append(_funcs[j])
                    i -= 1
                else:
                    array.append(_funcs[j])
                j -= 1

        array = array[::-1]
        if i >= 0:
            array = funcs[0:i + 1] + array
        elif j >= 0:
            array = _funcs[0:j + 1] + array
        return array

    def funcs(self):
        funcs = [(self.func, self.limits)]
        function = self.function
        if function.is_ConditionalBoolean:
            sub_funcs, function = function.funcs()
            funcs = sub_funcs + funcs

        return funcs, function

    def combine_clauses(self, rhs):
        func = []
        func.append([self.func, self.limits])
        return None, func, self.function, rhs

    def apply(self, axiom, *args, **kwargs):
        given = self
        
        if axiom.apply.__name__ == 'given':
            join = False
        elif 'join' in kwargs:
            join = kwargs['join']
            del kwargs['join']
        else:
            join = True
            
        if join and args and all(isinstance(eq, Boolean) for eq in args):
            for eq in args:
                given &= eq
            return given.apply(axiom, split=True, **kwargs)
        
        if 'depth' in kwargs:
            depth = kwargs['depth']
            if not depth:           
                del kwargs['depth']
                if 'split' in kwargs:
                    eqs = self.split()
                    self, *rest = eqs
                    args = tuple(rest) + args
                    del kwargs['split']
                return Boolean.apply(self, axiom, *args, **kwargs)
            else:
                kwargs['depth'] -= 1
        return self.this.function.apply(axiom, *args, **kwargs)

    @property
    def reversed(self):
        return self.this.function.reversed

    def __neg__(self):
        return self.this.function.__neg__()

    @property
    def definition(self):
        return self.this.function.definition

    def limits_include(self, eq):
        variables = self.variables_set
        _variables = eq.variables_set
        for v in variables:
            if v in _variables:
                _variables.remove(v)
            elif v.is_Slice:
                for _v in _variables:
                    if v.index_contains(_v):
                        _variables.remove(_v)
                        break

            else:
                continue
        return not _variables

    def __invert__(self):
        function = self.function.invert()
        return self.invert_type(function, *self.limits, counterpart=self)

    def invert(self):
        function = self.function.invert()
        return self.invert_type(function, *self.limits)

    def __and__(self, eq):
        """Overloading for & operator"""
        clue, funcs, lhs, rhs = self.combine_clauses(eq)
        function = lhs & rhs
        if not clue:
            clue = function.clue

        for func, limits in funcs[:-1]:
            function = func(function, *limits).simplify()
        func, limits = funcs[-1]

        if not clue:
            if function.equivalent is not None:
                clue = 'equivalent'
            elif function.given is not None:
                clue = 'given'

        kwargs = {}
        if clue:
            kwargs[clue] = [self, eq]

        return func(function, *limits, **kwargs).simplify()

    def bfn(self, bfn, eq):
        if self.is_Exists:
            func = self.func
            if eq.is_Exists:
                if self.limits == eq.limits:
                    limits = self.limits
                else:
                    limits = self.limits + eq.limits

                result = getattr(self.function, bfn)(eq.function)
            else:
                limits = self.limits
                result = getattr(self.function, bfn)(eq)
        else:
            if eq.is_Exists:
                if self.function.is_Exists and self.function.limits == eq.limits:
                    func = self.func
                    limits = self.limits
                    result = getattr(self.function, bfn)(eq)
                else:
                    limits = eq.limits
                    func = eq.func

                    dic = eq.limits_common(self)
                    if dic:
                        _self = self.func(self.function, *self.limits_delete(dic))

                        result = getattr(_self, bfn)(eq.function)
                        result.given = True
                    else:
                        result = self.bfn(bfn, eq.function)
            elif eq.is_ForAll:
                func = self.func
                if self.limits == eq.limits:
                    limits = self.limits
                else:
                    limits = self.limits + eq.limits
                result = getattr(self.function, bfn)(eq.function)
            else:
                func = self.func
                limits = self.limits
                result = getattr(self.function, bfn)(eq)

        equivalent = [self, eq] if eq.is_Boolean else self
        kwargs = {}
        if result.equivalent is not None:
            kwargs['equivalent'] = equivalent
        elif result.given is not None:
            kwargs['given'] = equivalent

        return func(result, *limits, **kwargs).simplify()

    @property
    def etype(self):
        return self.function.etype

    @property
    def lhs(self):
        return self.function.lhs

    @property
    def rhs(self):
        return self.function.rhs

    def __add__(self, eq):
        eq = sympify(eq)
        return self.bfn('__add__', eq)

    def __sub__(self, eq):
        eq = sympify(eq)
        return self.bfn('__sub__', eq)

    def __bool__(self):
        return False

    def subs(self, *args, simplify=True, **kwargs):
        args = tuple(map(sympify, args))
        
        def _subs_with_Equality(limits, old, new):
            _limits = []
            for limit in limits:
                x, *domain = limit
                if not domain:
                    ...
                elif len(domain) == 1:
                    domain, *_ = domain
                    if domain.is_set or not old._has(x):
                        limit = (x, domain._subs(old, new))
                else:                
                    _domain = []
                    for expr in domain:
                        _domain.append(expr._subs(old, new))
                    limit = (x, *_domain)
                _limits.append(limit)
            return _limits

        clue = None
        if len(args) == 1:
            clue, funcs, lhs, rhs = self.combine_clauses(args[0])
            function = lhs.subs(rhs, simplify=simplify)
            if not clue:
                clue = function.clue
                if not clue and function == lhs:
                    clue = 'equivalent'

            for func, limits in funcs[:-1]:
                if rhs.is_Equality:
                    limits = _subs_with_Equality(limits, *rhs.args)
                function = func(function, *limits).simplify()
            func, limits = funcs[-1]
            if rhs.is_Equality:
                limits = _subs_with_Equality(limits, *rhs.args)
        else:
            func = self.func
#             limits = self.limits
            limits = []          
            for x, *ab in self.limits:
                if x.is_Indexed or x.is_Slice:
                    indices = tuple(index._subs(*args, **kwargs) for index in x.indices)
                    if x.indices != indices:
                        x = x.func(x.base, *indices)                
                limits.append((x, *(e._subs(*args, **kwargs) for e in ab)))   
            
            if all(arg.is_Boolean for arg in args):
                function = self.function.subs(*args, **kwargs)
                clue = function.clue
            else:
                n, n1 = args
                if self.plausible:
                    function = self.function._subs(n, n1, **kwargs)
                    if n1._has(n):
                        assumptions = {'plausible':True}
                    else:
                        assumptions = {'given' : self}
                    eq = self.func(function, *limits, **assumptions)
                    if not n1._has(n):
                        return eq.simplify()
                    return eq
                else:
                    if n.is_symbol and n1 in n.domain:
                        function = self.function._subs(n, n1, **kwargs)
                        clue = 'given'
                    else:
                        function = self.function.subs(n, n1, **kwargs)
                        if function.clue is None:
                            return self
                        clue = function.clue

        kwargs = {}

        if clue:
            if isinstance(clue, dict):
                kwargs = clue
            else:
                kwargs[clue] = [self, *args] if all(isinstance(arg, Boolean) for arg in args) else self
        if function.is_BooleanAtom:
            return function.copy(**kwargs)

        return func(function, *limits, **kwargs).simplify()

    def simplify(self, deep=False):
        if self.function.equivalent is not None:
            self.function.equivalent = None

        if self.function.given is not None:
            self.function.given = None

        if self.function.imply is not None:
            self.function.imply = None

        if self.function.func == self.func:
            exists = self.function
            return self.func(exists.function, *exists.limits + self.limits, equivalent=self).simplify()

        this = self.delete_independent_variables()
        if this is not None:
            return this
        
        function = self.function
        if function.is_And or function.is_Or:
            for t in range(len(self.limits)):
                x, *domain = self.limits[t]            
                index = []
                for i, eq in enumerate(function.args):
                    if eq._has(x):
                        index.append(i)
                if len(index) == 1:
                    
                    if any(limit._has(x) for limit in self.limits[:t]):
                        continue
                    
                    index = index[0]
                    eqs = [*function.args]

                    eqs[index] = self.func(eqs[index], (x, *domain)).simplify()
                    limits = self.limits_delete(x)
                    
                    if limits:
                        function = function.func(*eqs, equivalent=None)
                        assert function.equivalent is None
                        return self.func(function, *limits, equivalent=self).simplify()
                    else:
                        function = function.func(*eqs, equivalent=self)
                        if function.equivalent is not None:
                            function = function.copy(equivalent=self)
                            
                        assert function.equivalent is self
                        return function
            limits_condition = self.limits_condition
            for i, eq in enumerate(self.function.args):
                eq &= limits_condition
                copy = False
                shrink = False
                if eq:
                    if self.function.is_Or:
                        copy = True
                    else:
                        shrink = True
                elif eq.is_BooleanFalse:
                    if self.function.is_And:
                        copy = True
                    else:
                        shrink = True

                if copy:
                    return eq.copy(equivalent=self)
                if shrink:
                    args = [*self.function.args]
                    del args[i]
                    function = self.function.func(*args)
                    return self.func(function, *self.limits, equivalent=self).simplify()

        if deep:
            function = self.function
            reps = {}
            for x, domain in limits_dict.items():
                if domain.is_set and domain.is_integer:
                    _x = x.copy(domain=domain)
                    function = function._subs(x, _x).simplify(deep=deep)
                    reps[_x] = x
            if reps:
                for _x, x in reps.items():
                    function = function._subs(_x, x)
                if function != self.function:
                    return self.func(function, *self.limits, equivalent=self).simplify()

        for i, (x, *domain) in enumerate(self.limits):
            if len(domain) == 1:
                domain = domain[0]
                if domain.is_FiniteSet: 
                    return self.func(self.finite_aggregate(x, domain), *self.limits_delete(x), equivalent=self).simplify()
                if domain.is_Contains:
                    if domain.lhs == x:
                        domain = domain.rhs
                        limits = self.limits_update({x:domain})
                        return self.func(self.function, *limits, equivalent=self).simplify()
                elif domain.is_ConditionSet:
                    if x == domain.variable:                        
                        condition = domain.condition
                    else:
                        condition = domain.condition._subs(domain.variable, x)                        
                        
                    limits = [*self.limits]
                    if domain.base_set.is_UniversalSet:
                        limits[i] = (x, condition)
                    else:
                        limits[i] = (x, condition, domain.base_set)
                    return self.func(self.function, *limits, equivalent=self).simplify()
                elif domain.is_UniversalSet:
                    limits = [*self.limits]
                    limits[i] = (x,)
                    return self.func(self.function, *limits, equivalent=self).simplify()

        for i, limit in enumerate(self.limits):
            if len(limit) == 1:
                continue            
            if len(limit) == 3:
                e, cond, baseset = limit
                if baseset.is_set:
                    if cond == self.function:
                        return BooleanTrue().copy(equivalent=self)
            else:
                e, s = limit
                if s.is_set:
                    if s.is_Symbol or s.is_Indexed:
                        continue
                    
                    if s.is_Piecewise:
                        if s.args[-1][0].is_EmptySet:
                            s = s.func(*s.args[:-2], (s.args[-2][0], True))                            
                        
                            limits = [*self.limits]
                            limits[i] = (e, s)
                            return self.func(self.function, *limits, equivalent=self).simplify()
                        continue
                    
                    image_set = s.image_set()
                    if image_set is not None:
                        expr, sym, base_set = image_set
                        if self.function.is_ExprWithLimits:
                            if sym in self.function.bound_symbols:
                                _sym = base_set.element_symbol(self.function.variables_set)
                                assert sym.shape == _sym.shape
                                _expr = expr._subs(sym, _sym)
                                if _expr == expr:
                                    for var in postorder_traversal(expr):
                                        if var._has(sym):
                                            break
                                    expr = expr._subs(var, var.definition)
                                    _expr = expr._subs(sym, _sym)
    
                                expr = _expr
                                sym = _sym
                            assert sym not in self.function.bound_symbols
                        
                        function = self.function
                        if e != expr:
                            if sym.type == e.type:
                                _expr = expr._subs(sym, e)                        
                                if _expr != e:
                                    _function = function._subs(e, expr)
                                    if _function == function:
                                        return self
                                    limits = self.limits_update({e : (sym, base_set)})
                                    function = _function          
                                else:
                                    base_set = base_set._subs(sym, e)
                                    limits = self.limits_update(e, base_set)
                            else:
                                _function = function._subs(e, expr)
                                if _function == function:
                                    return self
                                limits = self.limits_update({e : (sym, base_set)})
                                function = _function          
                        else:
                            limits = self.limits_update({e : (sym, base_set)})                            
                        return self.func(function, *limits, equivalent=self).simplify()
                else:  # s.type.is_condition: 
                    if s.is_Equality:
                        if e == s.lhs:
                            y = s.rhs
                        elif e == s.rhs:
                            y = s.lhs
                        else:
                            y = None
                        if y is not None and not y.has(e):
                            function = function._subs(e, y)
                            if function.is_BooleanAtom:
                                return function.copy(equivalent=self) 
                            limits = self.limits_delete(e)
                            if limits:
                                return self.func(function, equivalent=self)
                            function.equivalent = self
                            return function
                    if s == self.function or s.dummy_eq(self.function):  # s.invert() | self.function
                        return BooleanTrue().copy(equivalent=self)

        return ExprWithLimits.simplify(self, deep=deep)

    def limits_swap(self):
        this = ExprWithLimits.limits_swap(self)
        if this != self:
            this.equivalent = self
            return this
        return self

    def doit(self, **hints):
        function = self.function.doit(**hints)
        limits = []
        for i in range(len(self.limits) - 1, -1, -1):
            limit = self.limits[i]            
            if limit.is_intlimit:
                x, a, b = limit
                diff = b - a
                if diff.is_Number:
                    limits_behind = limits[::-1]
                    functions = []
                    for j in range(diff):
                        limits_before = [self.limits[t]._subs(x, a + j) for t in range(i)]                        
                        limits = limits_before + limits_behind 
                        
                        functions.append(self.func(function._subs(x, a + j), *limits).doit(**hints).simplify())
                                                
                    return self.operator(*functions, equivalent=self)
            else:
                limit = limit.doit()
                x, *ab = limit
                if x.is_Matrix:
                    if ab:
                        if x.is_BlockMatrix:
                            flat_list = x.args
                        else:
                            flat_list = x._mat
                            
                        for arg in flat_list[:0:-1]:
                            limits.append((arg,))
                        limits.append((flat_list[0], *ab))
                    else:
                        for arg in x._mat[::-1]:
                            limits.append((arg,))
                    continue
            
            limits.append(limit)
        return self.func(function, *limits[::-1], equivalent=self)


from sympy.concrete.limits import *
