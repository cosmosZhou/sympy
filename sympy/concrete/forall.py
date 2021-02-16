from sympy.logic.boolalg import Boolean, And, Or, relationship
from sympy.concrete.expr_with_limits import ExprWithLimits
from sympy.concrete.conditional_boolean import ConditionalBoolean
from sympy.core.sympify import sympify
from sympy.sets.sets import FiniteSet


class ForAll(ConditionalBoolean):
    """
    ForAll[p] q <=> !p | q
    """
    
    operator = And

    # this will change the default new operator!
    def __new__(cls, function, *symbols, **assumptions):
        if function.is_BooleanAtom or len(symbols) == 0:
            if not function:
                eqs = []
                from sympy import Equal
                for x, *ab in symbols:
                    if len(ab) == 1:
                        domain = ab[0]
                        if domain.is_set:
                            eqs.append(Equal(domain, domain.etype.emptySet))
                        elif domain.is_boolean:
                            eqs.append(domain.invert())
                if eqs:
                    return And(*eqs, **assumptions)
            return function.copy(**assumptions)
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            return ConditionalBoolean.subs(self, *args, **kwargs)
        old, new = args
        new = sympify(new)        
        if old in self.variables:
            wrt, *ab = self.limits[self.variables.index(old)]
            if len(ab) == 1:
                domain = ab[0]
            else:
                a, b = ab
                if b.is_set:
                    domain = b & old.domain_conditioned(a)
                else:
                    domain = Interval(a, b, right_open=wrt.is_integer, integer=wrt.is_integer)
                            
            eqs = []
            if not domain.is_set:
                domain = old.domain_conditioned(domain)

            from sympy.sets.contains import NotContains
            limit_cond = NotContains(new, domain).simplify()
            eqs.append(limit_cond)

            if self.function.is_Or:
                for equation in self.function.args:
                    eqs.append(equation._subs(old, new))
            else:
                eqs.append(self.function._subs(old, new))

            limits = self.limits_delete(old)
            if limits:
                for i, (x, *ab) in enumerate(limits):
                    if ab:
                        limits[i] = (x, *(expr._subs(old, new) for expr in ab))  
                            
                return self.func(Or(*eqs), *limits, given=self)
            else:
                return Or(*eqs, given=self).simplify()
                
        return ConditionalBoolean.subs(self, *args, **kwargs)
        
    def delete_independent_variables(self):
        limits_dict = self.limits_dict
        variables = self.variables

        deletes = set()
        function = self.function
        limits = self.limits
        needsToDelete = False
        for i, x in enumerate(variables):
            if not function._has(x):
                _needsToDelete = True
                for j in range(i):
                    dependent = variables[j]
                    domain = limits_dict[dependent]
                    if not isinstance(domain, list) and domain.has(x) and dependent not in deletes:
                        _needsToDelete = False
                        break

                if _needsToDelete:
                    needsToDelete = True
                    domain = limits_dict[x]
                    if not isinstance(domain, list) and domain.is_boolean:
                        free_symbols = domain.free_symbols & function.free_symbols
                        if free_symbols:
                            free_symbols = {sym for sym in free_symbols if not sym.is_given}
                            if free_symbols and domain.free_symbols - free_symbols - {x}:
                                limits = [*limits]
                                x, *_ = free_symbols
                                limits[i] = (x, domain)
                                break
                                                      
                    deletes.add(x)
            
            domain = limits_dict[x]
            if not isinstance(domain, list) and domain.is_FiniteSet and len(domain) == 1:
                needsToDelete = True
                deletes.add(x)
                _x, *_ = limits_dict[x].args
                function = function._subs(x, _x)
                    
        if needsToDelete:
            limits = limits_delete(limits, deletes)
            if limits:
                return self.func(function, *limits, equivalent=self).simplify()

            return function.copy(equivalent=self)
        
    def simplify(self, local=None, **kwargs):
        deletes = []
        for i in range(len(self.limits) - 1, -1, -1):
            x, *ab = self.limits[i]
            if not ab:
                deletes.append(x)
                continue
            if len(ab) == 1:
                domain = ab[0]
            else:
                a, b = ab
                if b.is_set:
                    continue
                domain = Interval(a, b, right_open=True, integer=x.is_integer)
                
            if self.function._has(x) and domain.is_set:
                _eval_domain_defined = self.function.domain_defined(x)
                if _eval_domain_defined in domain:
                    deletes.append(x)
                domain &= _eval_domain_defined
                if domain.is_FiniteSet:
                    if len(domain) == 1:
                        x0, *_ = domain
                        function = self.function._subs(x, x0)
                        if function.is_BooleanAtom:
                            return function.copy(equivalent=self)
                        
                        limits = [*self.limits]
                        del limits[i]
                        for j in range(i):
                            limits[j] = limits[j]._subs(x, x0)
                             
                        if limits:
                            return self.func(function, *limits, equivalent=self)
                        else:
                            function.equivalent = self
                            return function.simplify()

        if deletes:
            limits = self.limits_delete(deletes)
            if limits:
                return self.func(self.function, *limits, equivalent=self).simplify()

            if local:
                limits = [(x,) for x, *_ in self.limits if self.function._has(x)]
                return self.func(self.function, *limits, equivalent=self)
            return self.function.copy(equivalent=self)

        this = self.function.func.simplify_ForAll(self, *self.args)
        if this is not None:
            return this

        return ConditionalBoolean.simplify(self, **kwargs)
        
    def simplify_int_limits(self, function):
        for i, domain in self.limits_dict.items():
            if not i.is_integer or i.shape:
                continue

            i_expr = []
            patterns = []
            non_i_expr = set()
            from sympy import Wild
            _i = Wild('_i', **i.type.dict)
            for eq in function.args:
                if eq._has(i):
                    i_expr.append(eq)
                    patterns.append(eq._subs(i, _i))
                else:
                    non_i_expr.add(eq)

            matched_dic = {}
            for eq in non_i_expr:
                for pattern in patterns:
                    res = eq.match(pattern)
                    if not res:
                        continue

                    t, *_ = res.values()
                    if t in matched_dic:
                        matched_dic[t].add(eq)
                    else:
                        matched_dic[t] = {eq}
                    break

            new_set = set()
            for t, eqs in matched_dic.items():
                if len(eqs) != len(non_i_expr):
                    continue
                non_i_expr -= eqs
                new_set.add(t)

            if not new_set:
                continue

            eqs = i_expr + [*non_i_expr]

            limits = self.limits_update(i, domain | new_set)                
            
            function = function.func(*eqs)
            return function, limits
    
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
                if isinstance(domain, Complement):
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
        return '\N{FOR ALL}[%s](%s)' % (limits, p.doprint(self.function))

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
                    a, b = args
                    if b.is_set:
                        limit = var.domain_latex(a, baseset=b)
                    else:
                        limit = var.domain_latex(Interval(*args, right_open=var.is_integer, integer=var.is_integer))

                limits.append(limit)

            limit = r'\substack{%s}' % '\\\\'.join(limits)

        latex = r"\forall_{%s}{%s}" % (limit, latex)
        return latex

    def combine_clauses(self, rhs):
        if rhs.is_Exists:
            func = []
            if self.function.is_Exists:
                dic = self.function.limits_common(rhs)
                if dic:
                    limits = self.limits_intersect(rhs)
                    limits = limits_intersect(limits, self.function.limits)
                    func.append([ForAll.invert_type, limits])
                    return 'given', func, self.function.function, rhs.function

            dic = self.limits_common(rhs)
            if dic:
                limits = self.limits_delete(dic)
                if limits:
                    func.append([ForAll, limits])
                func.append([ForAll.invert_type, rhs.limits_update(dic)])
                return 'given', func, self.function, rhs.function

            func.append([ForAll, self.limits])
            func.append([ForAll.invert_type, rhs.limits])
            return None, func, self.function, rhs.function

        if rhs.is_ForAll:
            func = []

            if self.function.is_Exists:
                dic = self.function.limits_common(rhs)
                if dic:
                    func.append([ForAll.invert_type, self.function.limits])
                    func.append([ForAll, limits_intersect(self.limits, rhs.limits_delete(dic))])
                    return None, func, self.function.function, rhs.function
                dic = self.limits_common(rhs)
                if dic:
                    rhs_limits = rhs.limits_delete(dic)
                    if rhs_limits:
                        func.append([ForAll, rhs_limits])
                    else:
                        if rhs.function.is_Exists:
                            if self.function.limits_include(rhs.function): 
                                clue = relationship(self, rhs)                                
                                if clue: 
                                    func.append([ForAll.invert_type, self.function.limits])                                        
                                    func.append([ForAll, self.limits])
                                    return None, func, self.function.function, rhs.function.function
                                print('could not combine exists clauses due to different context')
                                return
                            elif rhs.function.limits_include(self.function):
                                clue = relationship(self, rhs)                                
                                if clue: 
                                    func.append([ForAll.invert_type, rhs.function.limits])
                                    func.append([ForAll, self.limits])
                                    return None, func, self.function.function, rhs.function.function
                                print('could not combine exists clauses due to different context')
                                return
                                
                            return ConditionalBoolean.combine_clauses(self, rhs)                                
                        else:
                            func.append([ForAll, self.limits])
                            return None, func, self.function, rhs.function
                    func.append([ForAll.invert_type, self.function.limits])
                    func.append([ForAll, self.limits])
                    return None, func, self.function.function, rhs.function

            if rhs.function.is_Exists:
                dic = self.limits_common(rhs.function)
                if dic:
                    func.append([ForAll.invert_type, rhs.function.limits])
                    func.append([ForAll, limits_intersect(self.limits_delete(dic), rhs.limits)])
                    return 'given', func, self.function, rhs.function.function
                else:
                    if self.limits_include(rhs): 
                        if any([limit.has(*rhs.function.variables) for limit in self.limits]):
                            dic = self.limits_common(rhs)                            
                            self_limits = self.limits_delete(dic)
                            if self_limits:
                                func.append([ForAll, self_limits])
                            func.append([ForAll.invert_type, rhs.function.limits])                        
                            func.append([ForAll, rhs.limits])                        
                            return 'given', func, self.function, rhs.function.function
                        else:
                            func.append([ForAll.invert_type, rhs.function.limits])
                            func.append([ForAll, self.limits])
                            return None, func, self.function, rhs.function.function                            
                    elif rhs.limits_include(self):
                        dic = self.limits_common(rhs)
                        self_limits = rhs.limits_delete(dic)
                        if self_limits:
                            func.append([ForAll, self_limits])
                        func.append([ForAll.invert_type, rhs.function.limits])
                        func.append([ForAll, limits_intersect(self.limits, rhs.limits)])
                        return 'given', func, self.function, rhs.function.function
                    else:
                        ...
            clue = {}
            limits = self.limits_intersect(rhs, clue=clue)
            func.append([ForAll, limits])
            if 'given' in clue:
                clue = 'given'
            else:
                clue = None
            return clue, func, self.function, rhs.function

        return ConditionalBoolean.combine_clauses(self, rhs)

    def __and__(self, eq):
        """Overloading for & operator"""
        if eq.is_ForAll: 
            if self.function == eq.function:
                limits = self.limits_union(eq)
                return self.func(self.function, *limits, equivalent=[self, eq]).simplify()
            
            if self.limits == eq.limits:
                if self.function.is_Exists and eq.function.is_Exists:
                    if self.function.limits == eq.function.limits:
                        if self.coexist_with(eq) is not False:
                            return ForAll(ForAll.invert_type(self.function.function & eq.function.function, *self.function.limits), *self.limits, equivalent=[self, eq]).simplify()
                                                    
        for i, (x, *ab) in enumerate(self.limits):
            if len(ab) == 1:
                cond, *_ = ab
                if cond.is_Unequality:
                    invert = cond.invert()
                    if self.function._subs(*invert.args) == eq:
                        limits = [self.limits]
                        del limits[i]                        
                        return self.func(self.function, *limits, equivalent=[self, eq]).simplify()                        
                    
        return ConditionalBoolean.__and__(self, eq)

    def apply(self, axiom, *args, **kwargs):
        for arg in args:
            if isinstance(arg, tuple):
                x, *_ = arg
                from sympy import Basic
                if isinstance(x, Basic) and x.is_symbol:
                    if x in self.free_symbols:
                        return self
                    elif x in self.variables_set:
                        index = self.variables.index(x)
                        x, domain = Tuple.as_setlimit(arg)
                        x, domain_given = Tuple.as_setlimit(self.limits[index])
                        if domain.is_set and domain_given.is_set:
                            if domain in domain_given:
                                ...
                            else:
                                print("variables' are beyond the bound given in ForAll context!")
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
            self.derivative = eqs
            return eqs
        elif isinstance(arr, tuple):
            for eq in arr:
                assert eq.parent is not None
                eq.parent = None

            return [self.func(eq, *self.limits, parent=self).simplify() for eq in arr]
        return self


from sympy.concrete.limits import *
