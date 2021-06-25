from sympy.logic.boolalg import Boolean, BooleanTrue
from sympy.concrete.expr_with_limits import ExprWithLimits
from sympy.core.sympify import sympify
from sympy.utilities.iterables import postorder_traversal


class ConditionalBoolean(Boolean, ExprWithLimits):
    """A boolean object is an object for which logic operations make sense."""
    
    __slots__ = []

    _op_priority = 12.1  # higher than Relational

    def __getitem__(self, rhs):
        return self.func(self.function[rhs], *self.limits)

    def __mul__(self, rhs):
        return self.func(self.function * rhs, *self.limits)
        
    def __mod__(self, rhs):
        return self.func(self.function % rhs, *self.limits)
    
    def __truediv__(self, rhs):
        return self.func(self.function / rhs, *self.limits)

    def __matmul__(self, rhs):
        return self.func(self.function @ rhs, *self.limits)
    
    def __rmatmul__(self, lhs):
        return self.func(lhs @ self.function, *self.limits)
    
    @property
    def T(self):
        return self.func(self.function.T, *self.limits)
    
    def inverse(self):
        return self.func(self.function.inverse(), *self.limits)

    def funcs(self):
        funcs = [(self.func, self.limits)]
        function = self.function
        if function.is_ConditionalBoolean:
            sub_funcs, function = function.funcs()
            funcs = sub_funcs + funcs

        return funcs, function

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
            args = [given, *args]
            given = And(*args, evaluate=False, equivalent=args)
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
        else:
            return Boolean.apply(self, axiom, *args, **kwargs)
        return self.this.function.apply(axiom, *args, **kwargs)

    @property
    def reversed(self):
        return self.func(self.function.reversed, *self.limits)

    def __neg__(self):
        return self.func(-self.function, *self.limits)

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
        return self.invert_type(function, *self.limits, negation=self)

    def invert(self):
        function = self.function.invert()
        return self.invert_type(function, *self.limits)

    def __and__(self, eq):
        """Overloading for & operator"""
        return Boolean.__and__(self, eq)

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
            elif eq.is_All:
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

    def simplify(self, deep=False):
        from sympy import S
        if self.function.func == self.func:
            exists = self.function
            return self.func(exists.function, *exists.limits + self.limits).simplify()

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
                    
                    if len(domain) == 1 and domain[0].is_boolean:
                        continue
                    
                    index = index[0]
                    eqs = [*function.args]

                    eqs[index] = self.func(eqs[index], (x, *domain)).simplify()
                    limits = self.limits_delete(x)
                    
                    if limits:
                        function = function.func(*eqs)                        
                        return self.func(function, *limits).simplify()
                    else:
                        return function.func(*eqs)
            limits_cond = self.limits_cond
            for i, eq in enumerate(self.function.args):
                eq &= limits_cond
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
                    return eq
                if shrink:
                    args = [*self.function.args]
                    del args[i]
                    function = self.function.func(*args)
                    return self.func(function, *self.limits).simplify()

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
                    return self.func(function, *self.limits).simplify()

        for i, (x, *domain) in enumerate(self.limits):
            if len(domain) == 1:
                domain = domain[0]
                if domain.is_FiniteSet and len(domain) == 1:
                    if len(self.limits) == 1: 
                        return self.func(self.finite_aggregate(x, domain), *self.limits_delete(x)).simplify()
                if domain.is_Contains:
                    if domain.lhs == x:
                        domain = domain.rhs
                        limits = self.limits_update({x:domain})
                        return self.func(self.function, *limits).simplify()
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
                    return self.func(self.function, *limits).simplify()
                elif domain.is_UniversalSet:
                    limits = [*self.limits]
                    limits[i] = (x,)
                    return self.func(self.function, *limits).simplify()

        for i, limit in enumerate(self.limits):
            if len(limit) == 1:
                continue            
            if len(limit) == 3:
                e, cond, baseset = limit
                if baseset.is_set:
                    if cond == self.function: 
                        return S.BooleanTrue
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
                            return self.func(self.function, *limits).simplify()
                        continue
                    
                    image_set = s.image_set()
                    if image_set is not None:
                        sym, expr, base_set = image_set
                        if self.function.is_ExprWithLimits:
                            if sym in self.function.bound_symbols:
                                _sym = base_set.element_symbol(self.function.variables_set)
                                assert sym.shape == _sym.shape
                                _expr = expr.subs(sym, _sym)
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
                                    limits = self.limits_update({e: (sym, base_set)})
                                    function = _function          
                                else:
                                    base_set = base_set._subs(sym, e)
                                    limits = self.limits_update(e, base_set)
                            else:
                                _function = function._subs(e, expr)
                                if _function == function:
                                    return self
                                limits = self.limits_update({e: (sym, base_set)})
                                function = _function          
                        else:
                            limits = self.limits_update({e: (sym, base_set)})                            
                        return self.func(function, *limits).simplify()
                else:  # s.type.is_condition: 
                    if s.is_Equal:
                        if e == s.lhs:
                            y = s.rhs
                        elif e == s.rhs:
                            y = s.lhs
                        else:
                            y = None
                        if y is not None and not y.has(e):
                            function = function._subs(e, y)
                            if function.is_BooleanAtom:
                                return function 
                            limits = self.limits_delete(e)
                            if limits:
                                return self.func(function, *limits)
                            return function
                    if s == self.function or s.dummy_eq(self.function):  # s.invert() | self.function
                        return S.BooleanTrue

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

                    return self.operator(*functions)
            else:
                limit = limit.doit()
                x, *ab = limit
                if x.is_Matrix:
                    if ab:
                        if x.is_BlockMatrix:
                            flat_list = x.args
                        else:
                            flat_list = x._args
                            
                        for arg in flat_list[:0:-1]:
                            limits.append((arg,))
                        limits.append((flat_list[0], *ab))
                    else:
                        for arg in x._args[::-1]:
                            limits.append((arg,))
                    continue

            limits.append(limit)
        return self.func(function, *limits[::-1])

    def _pretty(self, p, func):
        from sympy.printing.pretty.stringpict import prettyForm, stringPict                    
        prettyFunc = p._print("%s[%s]" % (func,
                                          ','.join([limit._format_ineq(p) for limit in self.limits])))
        prettyArgs = prettyForm(*p._print_seq([self.function], delimiter=', ').parens())
        
        pform = prettyForm(binding=prettyForm.FUNC, *stringPict.next(prettyFunc, prettyArgs))

        # store pform parts so it can be reassembled e.g. when powered
        pform.prettyFunc = prettyFunc
        pform.prettyArgs = prettyArgs

        return pform                

    def existent_symbols(self):
        free_symbols = Boolean.existent_symbols(self)        
        bound_symbols = {var.base: var.indices for var in self.bound_symbols if var.is_Slice}

        if bound_symbols:
            deletes = set()
            for symbol in free_symbols: 
                if symbol.is_Indexed:
                    base = symbol.base
                    if base in bound_symbols:
                        slices = bound_symbols[base]
                        if len(symbol.indices) == len(slices) and \
                        all(k >= b and b < e for k, (b, e) in zip(symbol.indices, slices)):
                            deletes.add(symbol)

            free_symbols -= deletes
            
        return free_symbols                    


from sympy.concrete.limits import *
