from sympy.logic.boolalg import Boolean, And, Or
from sympy.concrete.conditional_boolean import ConditionalBoolean
from sympy.sets.finiteset import FiniteSet
from sympy.concrete.expr_with_limits import ExprWithLimits


class Any(ConditionalBoolean):
    """
    Any[x:A] q(x) <=> conditionset(x, q(x), A) != Ø
    """
    
    operator = Or
    
    # this will change the default new operator!
    def __new__(cls, function, *symbols, **assumptions):
        if assumptions:
            from sympy.core.inference import Inference
            return Inference(Any.__new__(cls, function, *symbols), **assumptions)
        
        if function.is_BooleanAtom or len(symbols) == 0:
            return function.copy(**assumptions)
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)
    
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
                return self.func(function, *limits).simplify()
            
            if function.is_All:
                return function.simplify()
            return function
        
    def simplify(self, **kwargs):
        from sympy import S
        from sympy.sets.contains import Contains, NotContains
        if self.function.is_Equal:
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
                            return S.BooleanTrue
                elif domain.is_set:
                    t = self.variables.index(x)
                    if not any(limit._has(x) for limit in self.limits[:t]):
                        function = Contains(y, domain)
                        if function.is_BooleanTrue:
                            return function
                        limits = self.limits_delete(x)
                        if limits:
                            return self.func(function, *limits)
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
                    return self                          
#                     function = Unequal(S, x.emptySet)
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
                        return self.func(function, *limits).simplify()
                    else:
                        if function.is_BooleanAtom:
                            return function
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
                        function = Unequal(domain // S, x.emptySet)                        
                else:
                    function = None
                
                if function is not None:
                    limits = self.limits_delete((x,))
                    if limits:
                        return self.func(function, *limits).simplify()
                    else:
                        if function.is_BooleanAtom:
                            return function
                        return function
                    
        if self.function.is_And:
            limits_dict = self.limits_dict
            for i, eq in enumerate(self.function.args):
                if eq.is_Contains and eq.lhs in limits_dict:
                    domain = limits_dict[eq.lhs]
                    if isinstance(domain, list):
                        eqs = [*self.function.args]
                        del eqs[i]  
                        if not eq.rhs.has(*self.variables[:i]): 
                            return self.func(And(*eqs), *self.limits_update(eq.lhs, eq.rhs)).simplify()
                    elif domain == eq.rhs:
                        eqs = [*self.function.args]
                        del eqs[i]
                        return self.func(And(*eqs), *self.limits)

                if eq.is_Equal: 
                    if eq.lhs in limits_dict:
                        old, new = eq.args
                    elif eq.rhs in limits_dict:
                        new, old = eq.args
                    else:
                        continue
                    
                    continue 
                
        if self.function.is_Or:
            limits_dict = self.limits_dict
            for i, eq in enumerate(self.function.args):
                if eq.is_NotContains and eq.lhs in limits_dict:
                    domain = limits_dict[eq.lhs]
                    if not isinstance(domain, list) and domain in eq.rhs:
                        eqs = [*self.function.args]
                        del eqs[i]
                        return self.func(And(*eqs), *self.limits)

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
                     
                    return self.func(And(*eqs), *limits).simplify()
                
        if self.function.is_Equal:
            limits_dict = self.limits_dict
            x = None
            if self.function.lhs in limits_dict:
                x = self.function.lhs
                y = self.function.rhs
            elif self.function.rhs in limits_dict:
                x = self.function.rhs
                y = self.function.lhs

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
                            if domain.is_Range:
                                return self.func(self.function, (i, domain.start, domain.stop))
                            return self.func(self.function, (i, domain))

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        return '\N{THERE EXISTS}[%s](%s)' % (limits, p.doprint(self.function))

    def _pretty(self, p):
        return ConditionalBoolean._pretty(self, p, '\N{THERE EXISTS}')
    
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
        if self.function.is_LatticeOp:
            latex = r"\left(%s\right)" % latex

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
                    from sympy import Range
                    limit = var.domain_latex((Range if var.is_integer else Interval)(*args))

                limits.append(limit)

            limit = r'\substack{%s}' % '\\\\'.join(limits)

        latex = r"\exists_{%s}{%s}" % (limit, latex)
        return latex

    def __or__(self, eq):
        """Overloading for | operator"""
        if eq.is_Any:
            if self.limits == eq.limits:
                return self.func(self.function | eq.function, *self.limits)
                        
            if self.function == eq.function:
                limits = self.limits_union(eq)
                return self.func(self.function, *limits).simplify()
        
        return ConditionalBoolean.__or__(self, eq)

    @classmethod
    def simplify_All(cls, self, exists, *limits):
        if exists.function.is_All:
            forall = exists.function
            dic = self.limits_common(forall)
            if dic:
                forall = forall.func(forall.function, *forall.limits_update(dic))
                exists = exists.func(forall, *exists.limits)

                return self.func(exists, *limits_delete(limits, dic))
        
    def apply(self, axiom, *args, **kwargs):
        for arg in args:
            if isinstance(arg, tuple):
                x, *_ = arg
                from sympy import Basic
                if isinstance(x, Basic) and x.is_symbol:
                    if x in self.variables_set:
                        print('variables are given in Any context!')
                        return self
        
        return ConditionalBoolean.apply(self, axiom, *args, **kwargs)

from sympy.concrete.forall import All     
Any.invert_type = All
All.invert_type = Any

from sympy.concrete.limits import *
