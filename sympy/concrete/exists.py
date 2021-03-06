from sympy.logic.boolalg import Boolean, And, Or, BooleanTrue
from sympy.concrete.conditional_boolean import ConditionalBoolean
from sympy.sets.sets import FiniteSet


class Exists(ConditionalBoolean):
    """
    Exists[x:A] q(x) <=> conditionset(x, q(x), A) != Ø
    """
    
    operator = Or
    
    def combine_clauses(self, rhs):
        if rhs.is_Exists:
            func = []
            if rhs.function.is_ForAll:
                if rhs.function.function.is_Exists:
                    dic = self.limits_common(rhs.function.function)
                    if dic:
                        limits = self.limits_delete(dic)
                        limits = limits_intersect(rhs.limits, limits)
                        func.append([Exists, rhs.function.function.limits])
                        func.append([ForAll, rhs.function.limits])
                        func.append([Exists, limits])

                        return None, func, self.function, rhs.function.function.function
                dic = self.limits_common(rhs.function)
                if dic:
                    func.append([ForAll, rhs.function.limits])
                    limits = self.limits_delete(dic)
                    func.append([Exists, rhs.limits_intersect(limits)])
                    return 'given', func, self.function, rhs.function.function
            limits = self.limits_intersect(rhs)
            if self.variables_set == rhs.variables_set:
                clue = 'equivalent'
            else:
                clue = None
            func.append([Exists, limits])
            return clue, func, self.function, rhs.function

        if rhs.is_ForAll:
            func = []
            if rhs.function.is_Exists:
                dic = self.limits_common(rhs.function)
                if dic:
                    clue = None
                    func.append([Exists, rhs.function.limits])
                    limits = self.limits_delete(dic)

                    dic = self.limits_common(rhs)
                    if dic:
                        clue = 'given'
                        rhs_limits = rhs.limits_delete(dic)
                        if rhs_limits:
                            func.append([ForAll, rhs_limits])
                    else:
                        func.append([ForAll, rhs.limits])

                    if limits:
                        func.append([Exists, limits])

                    return clue, func, self.function, rhs.function.function

            if self.function.is_ForAll:
                rhs_limits = rhs.limits_intersect(self.function)
                dic = self.limits_common(rhs)
                if dic:
                    rhs_limits = limits_delete(rhs_limits, dic)
                    if rhs_limits:
                        func.append([ForAll, rhs_limits])
                    func.append([Exists, self.limits])
                    return 'given', func, self.function.function, rhs.function
    
                func.append([ForAll, rhs_limits])
                func.append([Exists, self.limits])
                return None, func, self.function.function, rhs.function
            else:
                dic = self.limits_common(rhs)
                if dic:
                    rhs_limits = rhs.limits_delete(dic)
                    if rhs_limits:
                        func.append([ForAll, rhs_limits])
                    func.append([Exists, self.limits])
                    return 'given' if rhs.plausible else None, func, self.function, rhs.function
    
                func.append([ForAll, rhs.limits])
                func.append([Exists, self.limits])
                return None, func, self.function, rhs.function

        return ConditionalBoolean.combine_clauses(self, rhs)

    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            if 'var' in kwargs:
                assert len(args) == 0
                args = [self.limits_dict[kwargs.pop('var')]]

            if len(args) == 1:
                eq, *_ = args
                if self.function.is_And:
                    if eq in self.function.args:
                        function = self.function.subs(eq)
                        clue = function.clue
                        
                        kwargs.clear()
                        kwargs[clue] = self
                        return self.func(function, *self.limits, **kwargs).simplify()
                    
                if eq.is_Exists and eq.limits == self.limits:                    
                    if eq.is_given_by(self):
                        function = self.function.subs(eq.function)
                        return self.func(function, *self.limits, given=self).simplify()
                
        return ConditionalBoolean.subs(self, *args, **kwargs)

    def delete_independent_variables(self):
        limits_dict = self.limits_dict
        variables = self.variables

        deletes = set()
        function = self.function
        for i, x in enumerate(variables):
            if not function._has(x):
                needsToDelete = True
                for j in range(i):
                    dependent = variables[j]
                    domain = limits_dict[dependent]
                    if not isinstance(domain, list) and domain.has(x) and dependent not in deletes:
                        needsToDelete = False
                        break

                if needsToDelete:
                    deletes.add(x)
            
            domain = limits_dict[x]
            if isinstance(domain, tuple) and domain.is_FiniteSet and len(domain) == 1:
                needsToDelete = True
                deletes.add(x)
                _x, *_ = limits_dict[x].args
                function = function._subs(x, _x)
                    
        if deletes:
            limits = self.limits_delete(deletes)
            if limits:
                return self.func(function, *limits, equivalent=self).simplify()

            return function.copy(equivalent=self)
        
    def simplify(self, **kwargs):
        from sympy.sets.contains import Contains, NotContains
        if self.function.is_Equality:
            limits_dict = self.limits_dict
            x = None
            if self.function.lhs in limits_dict:
                x = self.function.lhs
                y = self.function.rhs
            elif self.function.rhs in limits_dict:
                x = self.function.rhs
                y = self.function.lhs

            if x is not None and not y.has(x):
                domain = limits_dict[x]
                if isinstance(domain, list):
                    if len(self.limits) == 1:
                        if all(not var.is_given for var in y.free_symbols):
                            return BooleanTrue().copy(equivalent=self)
                elif domain.is_set:
                    t = self.variables.index(x)
                    if not any(limit._has(x) for limit in self.limits[:t]):
                        function = Contains(y, domain)
                        if function.is_BooleanTrue:
                            return function.copy(equivalent=self)
                        limits = self.limits_delete(x)
                        if limits:
                            return self.func(function, *limits, equivalent=self)
                        function.equivalent = self
                        return function
                    
        from sympy import Unequal, Equal
        if self.function.is_Contains:            
            limits_dict = self.limits_dict
            x = None
            if self.function.lhs in limits_dict:
                x = self.function.lhs
                S = self.function.rhs                
            
            if x is not None:
                domain = limits_dict[x]
                if isinstance(domain, list):                          
                    function = Unequal(S, x.emptySet)
                elif domain.is_set:
                    if domain.is_FiniteSet:
                        function = Contains(domain.arg, S)
                    else:
                        function = Unequal(S & domain, x.emptySet)                        
                else:
                    function = None
                
                if function is not None:
                    limits = self.limits_delete((x,))
                    if limits:
                        return self.func(function, *limits, equivalent=self).simplify()
                    else:
                        if function.is_BooleanAtom:
                            return function.copy(equivalent=self)
                        
                        function.equivalent = self
                        return function

        elif self.function.is_NotContains:            
            limits_dict = self.limits_dict
            x = None
            if self.function.lhs in limits_dict:
                x = self.function.lhs
                S = self.function.rhs
                
            if x is not None:
                domain = limits_dict[x]
                if isinstance(domain, list):                          
                    function = Equal(S, x.emptySet)
                elif domain.is_set:
                    if domain.is_FiniteSet:
                        function = NotContains(domain.arg, S)
                    else:
                        function = Unequal(domain - S, x.emptySet)                        
                else:
                    function = None
                
                if function is not None:
                    limits = self.limits_delete((x,))
                    if limits:
                        return self.func(function, *limits, equivalent=self).simplify()
                    else:
                        if function.is_BooleanAtom:
                            return function.copy(equivalent=self)
                        function.equivalent = self
                        return function
                    
        if self.function.is_And:
            limits_dict = self.limits_dict
            for i, eq in enumerate(self.function.args):
                if eq.is_Contains and eq.lhs in limits_dict :
                    domain = limits_dict[eq.lhs]
                    if isinstance(domain, list):
                        eqs = [*self.function.args]
                        del eqs[i]  
                        if not eq.rhs.has(*self.variables[:i]):                  
                            return self.func(And(*eqs), *self.limits_update(eq.lhs, eq.rhs), equivalent=self).simplify()
                    elif domain == eq.rhs:
                        eqs = [*self.function.args]
                        del eqs[i]                    
                        return self.func(And(*eqs), *self.limits, equivalent=self)

                if eq.is_Equality:
                    if eq.lhs in limits_dict:
                        old, new = eq.args
                    elif eq.rhs in limits_dict:
                        new, old = eq.args
                    else:
                        continue
                    
                    print("this simplification should be aximatized!")
                    limits = self.limits_delete(old)
                    if any(limit._has(old) for limit in limits):
                        continue
                    
                    eqs = [*self.function.args] 
                    del eqs[i]
                    eqs = [eq._subs(old, new) for eq in eqs]
                    
                    domain = limits_dict[old]
                    if isinstance(domain, list):
                        limit = (old,)
                    else:
                        limit = (old, domain)
                    eq = self.func(eq, limit).simplify()                    
                    eqs.append(eq)
                     
                    return self.func(And(*eqs), *limits, equivalent=self).simplify()
                
        if self.function.is_Or:
            limits_dict = self.limits_dict
            for i, eq in enumerate(self.function.args):
                if eq.is_NotContains and eq.lhs in limits_dict :
                    domain = limits_dict[eq.lhs]
                    if not isinstance(domain, list) and domain in eq.rhs:
                        eqs = [*self.function.args]
                        del eqs[i]                    
                        return self.func(And(*eqs), *self.limits, equivalent=self)

                if eq.is_Unequal:
                    continue
                    if eq.lhs in limits_dict:
                        old, new = eq.args
                    elif eq.rhs in limits_dict:
                        new, old = eq.args
                    else:
                        continue
                    
                    limits = self.limits_delete(old)
                    if any(limit._has(old) for limit in limits):
                        continue
                    
                    eqs = [*self.function.args] 
                    del eqs[i]
                    eqs = [eq._subs(old, new) for eq in eqs]
                    
                    domain = limits_dict[old]
                    if isinstance(domain, list):
                        limit = (old,)
                    else:
                        limit = (old, domain)
                    eq = self.func(eq, limit).simplify()                    
                    eqs.append(eq)
                     
                    return self.func(And(*eqs), *limits, equivalent=self).simplify()
                
        if self.function.is_Equality:
            limits_dict = self.limits_dict
            x = None
            if self.function.lhs in limits_dict:
                x = self.function.lhs
                y = self.function.rhs
            elif self.function.rhs in limits_dict:
                x = self.function.rhs
                y = self.function.lhs

            if x is not None and not y._has(x):
                domain = limits_dict[x]
                if isinstance(domain, Boolean):
                    print('this should be axiomatized!')
                    function = domain._subs(x, y)
                    if function.is_BooleanAtom:
                        return function.copy(equivalent=self)
                    
                    limits = self.limits_delete(x)
                    if limits:
                        return self.func(function, *limits, equivalent=self)
                    function.equivalent = self
                    return function
                
        return ConditionalBoolean.simplify(self, **kwargs)

    def union_sets(self, expr):
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b + 1) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))
            elif len(args) == 1:
                domain = args[0]
                if domain.is_Complement:
                    A, B = domain.args
                    if isinstance(B, FiniteSet):
                        deletes = set()
                        for b in B:
                            if self.function.subs(i, b) == expr:
                                deletes.add(b)
                        if deletes:
                            B -= FiniteSet(*deletes)
                            if B:
                                domain = Complement(A, B, evaluate=False)
                                return self.func(self.function, (i, domain))
                            domain = A
                            if isinstance(domain, Interval) and domain.is_integer:
                                return self.func(self.function, (i, domain.min(), domain.max() + 1))
                            return self.func(self.function, (i, domain))

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        return '∃［%s］(%s)' % (limits, p.doprint(self.function))

    def int_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 3:
            return limit

    def condition_limit(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        if len(limit) == 2:
            return limit

    def expr_iterable(self):
        function = self.function

        if isinstance(function, FiniteSet):
            if len(function) == 1:
                expr, *_ = function
                if expr.is_Indexed:
                    if len(expr.indices) == 1:
                        return expr.base
                    return expr.base[expr.indices[:-1]]

    def _latex(self, p):
        latex = p._print(self.function)

        if all(len(limit) == 1 for limit in self.limits):
            limit = ', '.join(var.latex for var, *_ in self.limits)
        else:
            limits = []
            for limit in self.limits:
                var, *args = limit
                if len(args) == 0:
                    limit = var.latex
                elif len(args) == 1:
                    limit = var.domain_latex(args[0])
                else:
                    limit = var.domain_latex(Interval(*args, right_open=var.is_integer, integer=var.is_integer))

                limits.append(limit)

            limit = r'\substack{%s}' % '\\\\'.join(limits)

        latex = r"\exists_{%s}{%s}" % (limit, latex)
        return latex

    def __and__(self, eq):
        """Overloading for & operator"""
        if eq.is_Exists:
            if self.limits == eq.limits:
                if self.coexist_with(eq) is not False:
                    return ConditionalBoolean.__and__(self, eq)
            return And(self, eq, equivalent=[self, eq])
        
        return ConditionalBoolean.__and__(self, eq)

    @classmethod
    def simplify_ForAll(cls, self, exists, *limits):
        if exists.function.is_ForAll:
            forall = exists.function
            dic = self.limits_common(forall)
            if dic:
                forall = forall.func(forall.function, *forall.limits_update(dic))
                exists = exists.func(forall, *exists.limits)

                return self.func(exists, *limits_delete(limits, dic), equivalent=self)
        
    def apply(self, axiom, *args, **kwargs):
        for arg in args:
            if isinstance(arg, tuple):
                x, *_ = arg
                from sympy import Basic
                if isinstance(x, Basic) and x.is_symbol:
                    if x in self.variables_set:
                        print('variables are given in Exists context!')
                        return self
        
        return ConditionalBoolean.apply(self, axiom, *args, **kwargs)

    def split(self, *args, **kwargs):
        arr = self.function.split(*args, **kwargs)
        if isinstance(arr, list):
            clue = None
            for eq in arr:
                if eq.given is None:
                    if eq.equivalent is None:
                        assert eq.imply is not None
                        if clue is None:
                            clue = 'imply'
                            self.function.derivative = None 
                        eq.imply = None
                        continue
                    if eq.equivalent.given is None:
                        print('eq.equivalent.given is None')
                    else:
                        eq.equivalent.given = None
                        eq.equivalent = None
                else:
                    eq.given = None
                    if clue is None:
                        clue = 'given'
                assert eq.equivalent is None 
            eqs = [self.func(eq, *self.limits, **{clue: self}) for eq in arr]
            if kwargs.get('simplify', True):
                eqs = [eq.simplify() for eq in eqs]
                
            if self.function.is_Or:
                self.derivative = eqs
# exists with and structure is not deductive, only deductive for or structure!
            return eqs
        elif isinstance(arr, tuple):
            for eq in arr:
                assert eq.parent is not None
                eq.parent = None

            return [self.func(eq, *self.limits, parent=self).simplify() for eq in arr]
        return self

    
from sympy.concrete.forall import ForAll     
Exists.invert_type = ForAll
ForAll.invert_type = Exists

from sympy.concrete.limits import *
