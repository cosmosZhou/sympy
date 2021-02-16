from sympy.core.add import Add
from sympy.core.compatibility import is_sequence
from sympy.core.containers import Tuple
from sympy.core.expr import Expr
from sympy.core.mul import Mul
from sympy.core.relational import Relational
from sympy.core.singleton import S
from sympy.core.symbol import Symbol, Dummy, Wild
from sympy.core.sympify import sympify
from sympy.functions.elementary.piecewise import (piecewise_fold,
    Piecewise)
from sympy.logic.boolalg import BooleanFunction, Boolean, And, Or
    
from sympy.matrices import Matrix
from sympy.tensor.indexed import Idx, Indexed, Slice
from sympy.sets.sets import Interval, Set, FiniteSet, Union, Intersection
from sympy.sets.fancysets import Range
from sympy.utilities import flatten
from sympy.utilities.iterables import sift, postorder_traversal
from sympy.functions.elementary.extremum import Min, Max
from _functools import reduce
from sympy.matrices.expressions.blockmatrix import BlockMatrix
from sympy.core.logic import fuzzy_and

def _common_new(cls, function, *symbols, **assumptions):
    """Return either a special return value or the tuple,
    (function, limits, orientation). This code is common to
    both ExprWithLimits and AddWithLimits."""
    function = sympify(function)

    if function is S.NaN:
        return S.NaN

    if symbols:
        limits, orientation = _process_limits(*symbols)
        for i, li in enumerate(limits):
            if len(li) == 4:
                function = function.subs(li[0], li[-1])
                limits[i] = tuple(li[:-1])
                
            if len(li) == 3:
                oldsymbol = li[0] 
# added here to remove the domain of this variable!
                if isinstance(oldsymbol, Symbol) and oldsymbol.is_bounded:
                    newsymbol = oldsymbol.unbounded
                    function = function._subs(oldsymbol, newsymbol)
                    limits[i] = Tuple(newsymbol, *li[1:])
 
    else:
        # symbol not provided -- we can still try to compute a general form
#         free = function.free_symbols
#         if len(free) != 1:
#             raise ValueError(
#                 "specify dummy variables for %s" % function)
#         limits, orientation = [Tuple(s) for s in free], 1
        limits, orientation = [], 1

    # denest any nested calls
    while cls == type(function):
        limits = list(function.limits) + limits
        function = function.function

    # Any embedded piecewise functions need to be brought out to the
    # top level. We only fold Piecewise that contain the integration
    # variable.
    reps = {}
    symbols_of_integration = set([i[0] for i in limits])
    for p in function.atoms(Piecewise):
        if not p.has(*symbols_of_integration):
            reps[p] = Dummy()
    # mask off those that don't
    function = function.xreplace(reps)
    # do the fold
    function = piecewise_fold(function)
    # remove the masking
    function = function.xreplace({v: k for k, v in reps.items()})

    return function, limits, orientation


def _process_limits(*symbols):
    """Process the list of symbols and convert them to canonical limits,
    storing them as Tuple(symbol, lower, upper). The orientation of
    the function is also returned when the upper limit is missing
    so (x, 1, None) becomes (x, None, 1) and the orientation is changed.
    """
    limits = []
    orientation = 1
    for V in symbols:
        if isinstance(V, (Relational, BooleanFunction)):
            variable = V.atoms(Symbol).pop()
            V = (variable, V.as_set())

        if isinstance(V, Symbol) or getattr(V, '_diff_wrt', False):
            if isinstance(V, Idx):
                if V.lower is None or V.upper is None:
                    limits.append(Tuple(V))
                else:
                    limits.append(Tuple(V, V.lower, V.upper))
            else:
                limits.append(Tuple(V))
            continue
        elif is_sequence(V, Tuple):
            if len(V) >= 2:
                if isinstance(V[1], Boolean):
                    limits.append(Tuple(*V))
                    continue            
                if len(V) == 2:
                    if isinstance(V[1], Range):
                        lo = V[1].inf
                        hi = V[1].sup
                        dx = abs(V[1].step)
                        V = [V[0]] + [0, (hi - lo) // dx, dx * V[0] + lo]
                    elif isinstance(V[1], set):
                        V = V[0], FiniteSet(*V[1])
            V = sympify(flatten(V))  # a list of sympified elements
            if isinstance(V[0], (Symbol, Idx)) or getattr(V[0], '_diff_wrt', False):
                newsymbol = V[0]
                if len(V) == 2 and isinstance(V[1], Interval):  # 2 -> 3
                    # Interval
                    V[1:] = [V[1].min(), V[1].max() + 1 if newsymbol.is_integer else V[1].max()]   
                elif len(V) == 3:
                    # general case
                    if V[2] is None and not V[1] is None:
                        orientation *= -1
                        
                    V = [newsymbol] + [i for i in V[1:] if i is not None]

                if not isinstance(newsymbol, Idx) or len(V) == 3:
                    if len(V) == 4:
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 3:
                        if isinstance(newsymbol, Idx):
                            # Idx represents an integer which may have
                            # specified values it can take on; if it is
                            # given such a value, an error is raised here
                            # if the summation would try to give it a larger
                            # or smaller value than permitted. None and Symbolic
                            # values will not raise an error.
                            lo, hi = newsymbol.lower, newsymbol.upper
                            try:
                                if lo is not None and not bool(V[1] >= lo):
                                    raise ValueError("Summation will set Idx value too low.")
                            except TypeError:
                                pass
                            try:
                                if hi is not None and not bool(V[2] <= hi):
                                    raise ValueError("Summation will set Idx value too high.")
                            except TypeError:
                                pass
                            
                        limits.append(Tuple(*V))
                        continue
                    if len(V) == 1 or (len(V) == 2 and V[1] is None):
                        limits.append(Tuple(newsymbol))
                        continue
                    elif len(V) == 2:
                        limits.append(Tuple(newsymbol, V[1]))
                        continue

        raise ValueError('Invalid limits given: %s' % str(symbols))

    return limits, orientation


class ExprWithLimits(Expr):
    __slots__ = ['is_commutative']

    def _eval_is_integer(self):
        return self.function.is_integer

    def _eval_is_random(self):
        return self.function.is_random

    def finite_aggregate(self, x, s):
        args = []
        if len(s) > 1:
            if self.operator.is_Add:
                s &= self.function.domain_nonzero(x)
            if s.is_Complement:
                return self                
            if s.is_EmptySet:
                return self.operator.identity
            if s.is_Intersection:
                finiteset = []
                for e in s.args:
                    if e.is_FiniteSet:
                        finiteset.append(e)
                if len(finiteset) == 1:
                    s = finiteset[0]
            assert s.is_FiniteSet, str(s) 
        for k in s:
            if x == k: 
                expr = self.function
            else:
                expr = self.function._subs(x, k)
            args.append(expr.simplify())
        return self.operator(*args)         

    def subs_limits_with_epitome(self, epitome):
        if epitome.func == self.func and len(epitome.limits) == len(self.limits):
            _self = self
            for _v, v in zip(epitome.variables, self.variables):
                if _v != v:
                    _self = _self.limits_subs(v, _v)
            return _self
        return self

    def limits_intersect(self, expr, clue=None):
        return limits_intersect(self.limits, expr.limits, clue=clue)

    def limits_union(self, expr):
        return limits_union(self.limits, expr.limits)

# precondition, self and other are structurally equal!
    def _dummy_eq(self, other):
        _self = other
        for (x, *_), (_x, *_) in zip(other.limits, self.limits):
            if x != _x:
                _self = _self.limits_subs(x, _x)
                if not _self.is_ExprWithLimits:
                    return False
        return _self.limits == self.limits and _self.function._dummy_eq(self.function)

    @property
    def limits_dict(self):
        return limits_dict(self.limits)

    @property
    def limits_condition(self):
        return limits_condition(self.limits)

    def limits_update(self, *args):
        return limits_update(self.limits, *args)

    def limits_delete(self, dic):
        return limits_delete(self.limits, dic)

    def limits_common(self, eq, is_or=False):
        return limits_common(self.limits, eq.limits, is_or)

    @property
    def dtype(self):
        return self.function.dtype
        
    def __new__(cls, function, *symbols, **assumptions):
        function = sympify(function)
        limits = []
        symbols = [*symbols]
        for i in range(len(symbols) - 1, -1, -1):
            sym = symbols[i]
            if isinstance(sym, tuple):
                sym = Tuple(*sym)
            
            if isinstance(sym, Tuple): 
                if len(sym) == 2:
                    if sym[1].is_BooleanTrue:
                        return function.copy(**assumptions)                    
                    x, domain = sym
                    if domain.is_set:
                        assert x.type in domain.etype or domain.etype in x.type, "domain.etype = %s\n, x.type = %s" % (domain.etype, x.type)
                        if x.is_Symbol and x.is_bounded:
                            domain &= x.domain_bounded
                            _x = x.unbounded
#                             assert x.type == _x.type
                            sym = _x, domain
                            function = function._subs(x, _x)                            
                        elif domain.is_Interval and x.is_integer:
                            if domain.is_UniversalSet:
                                sym = (x,)
                            else:
                                sym = (x, domain.min(), domain.max() + 1)
                elif len(sym) == 3: 
                    x, *ab = sym
                    if x.is_Symbol and x.is_bounded and not ab[0].is_boolean:
                        _x = x.unbounded
                        function = function._subs(x, _x)
                        sym = (_x, *ab)
                        
                    a, b = ab
                    if a.is_boolean:
                        if a.is_BooleanTrue:
                            if b.is_Interval and x.is_integer:
                                if b.is_UniversalSet:
                                    sym = (x,)
                                else:
                                    sym = (x, b.min(), b.max() + 1)
                            else:
                                sym = (x, b)
                    elif x.is_integer and not x.shape and not x.is_set and not b.is_set:
                        if a == b - 1:
                            function = function._subs(x, a)                        
                            for j in range(i - 1, -1, -1):
                                _x, *ab = symbols[j]                            
                                ab = [e._subs(x, a) for e in ab]
                                symbols[j] = (_x, *ab)
                                if _x == x:
                                    break                            
                                
                            continue
                        elif a == b:
                            return cls.identity(function, **assumptions)
                        
                limits.append(Tuple(*sym))
            else:
                limits.append(Tuple(sym,))
                
        limits.reverse()
    # denest any nested calls
        while cls == type(function):
            limits = list(function.limits) + limits
            function = function.function

        if not limits and symbols:
            return function.copy(**assumptions)
        
        args = [function] + limits       
        
        if cls.is_Boolean:
            obj = Boolean.__new__(cls, *args, **assumptions)
        else:
            obj = Expr.__new__(cls, *args, **assumptions)

        return obj

    @property
    def function(self):
        """Return the function applied across limits.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x
        >>> Integral(x**2, (x,)).function
        x**2

        See Also
        ========

        limits, variables, free_symbols
        """
        return self._args[0]

    @property
    def limits(self):
        """Return the limits of expression.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i
        >>> Integral(x**i, (i, 1, 3)).limits
        ((i, 1, 3),)

        See Also
        ========

        function, variables, free_symbols
        """
        return self._args[1:]

    @property
    def variables(self):
        """Return a list of the limit variables.

        >>> from sympy import Sum
        >>> from sympy.abc import x, i
        >>> Sum(x**i, (i, 1, 3)).variables
        [i]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return [l[0] for l in self.limits]

    @property
    def variable(self):
        return self.limits[0][0]

    @property
    def variables_set(self):
        return {l[0] for l in self.limits}

    @property
    def bound_symbols(self):
        """Return only variables that are dummy variables.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x, i, j, k
        >>> Integral(x**i, (i, 1, 3), (j, 2), k).bound_symbols
        [i, j]

        See Also
        ========

        function, limits, free_symbols
        as_dummy : Rename dummy variables
        transform : Perform mapping on the dummy variable
        """
        return [l[0] for l in self.limits if len(l) != 1]

    @property
    def free_symbols(self):
        """
        This method returns the symbols in the object, excluding those
        that take on a specific value (i.e. the dummy symbols).

        Examples
        ========

        >>> from sympy import Sum
        >>> from sympy.abc import x, y
        >>> Sum(x, (x, y, 1)).free_symbols
        {y}
        """
        # don't test for any special values -- nominal free symbols
        # should be returned, e.g. don't return set() if the
        # function is zero -- treat it like an unevaluated expression.
        function, limits = self.function, self.limits
        isyms = function.free_symbols
        for xab in limits:
#             if len(xab) == 1:
#                 isyms.add(xab[0])
#                 continue
            # take out the target symbol
            x, *ab = xab
            if x in isyms:
                isyms.remove(x)
            # add in the new symbols
            isyms -= {var for var in isyms if var._has(x)}
            
            for i in ab:
                isyms.update(i.free_symbols)            
        return isyms

    @property
    def is_number(self):
        """Return True if the Sum has no free symbols, else False."""
        return not self.free_symbols

    def _eval_interval(self, x, a, b):
        limits = [(i if i[0] != x else (x, a, b)) for i in self.limits]
        integrand = self.function
        return self.func(integrand, *limits)

    def _eval_subs(self, old, new):
        """
        Perform substitutions over non-dummy variables
        of an expression with limits.  Also, can be used
        to specify point-evaluation of an abstract antiderivative.

        Examples
        ========

        >>> from sympy import Sum, oo
        >>> from sympy.abc import s, n
        >>> Sum(1/n**s, (n, 1, oo)).subs(s, 2)
        Sum(n**(-2), (n, 1, oo))

        >>> from sympy import Integral
        >>> from sympy.abc import x, a
        >>> Integral(a*x**2, x).subs(x, 4)
        Integral(a*x**2, (x, 4))

        See Also
        ========

        variables : Lists the integration variables
        transform : Perform mapping on the dummy variable for integrals
        change_index : Perform mapping on the sum and product dummy variables

        """
        from sympy.core.function import AppliedUndef, UndefinedFunction
        func, limits = self.function, list(self.limits)

        # If one of the expressions we are replacing is used as a func index
        # one of two things happens.
        #   - the old variable first appears as a free variable
        #     so we perform all free substitutions before it becomes
        #     a func index.
        #   - the old variable first appears as a func index, in
        #     which case we ignore.  See change_index.

        # Reorder limits to match standard mathematical practice for scoping
        limits.reverse()

        if not isinstance(old, Symbol) or \
                old.free_symbols.intersection(self.free_symbols):
            sub_into_func = True
            for i, xab in enumerate(limits):
                if 1 == len(xab) and old == xab[0]:
                    if new._diff_wrt:
                        xab = (new,)
                    else:
                        xab = (old, old)
                limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                if self.func.__name__ in ('Sum', 'Product', 'Integral'):
                    if len(xab[0].free_symbols.intersection(old.free_symbols)) != 0:
                        sub_into_func = False
                        break

            if isinstance(old, AppliedUndef) or isinstance(old, UndefinedFunction):
                sy2 = set(self.variables).intersection(set(new.atoms(Symbol)))
                sy1 = set(self.variables).intersection(set(old.args))
                if not sy2.issubset(sy1):
                    raise ValueError(
                        "substitution can not create dummy dependencies")
                sub_into_func = True
            if sub_into_func:
                func = func.subs(old, new)
        else:
            # old is a Symbol and a dummy variable of some limit
            for i, xab in enumerate(limits):
                if len(xab) == 3:
                    limits[i] = Tuple(xab[0], *[l._subs(old, new) for l in xab[1:]])
                    if old == xab[0]:
                        break
        # simplify redundant limits (x, x)  to (x, )
        for i, xab in enumerate(limits):
            if len(xab) == 2 and (xab[0] - xab[1]).is_zero:
                limits[i] = Tuple(xab[0],)

        # Reorder limits back to representation-form
        limits.reverse()

        return self.func(func, *limits)

    def as_multiple_terms(self, x, domain): 
        from sympy import Complement    
        universalSat = Interval(S.NegativeInfinity, S.Infinity, integer=True)
        args = []
        union = x.emptySet 
        assert x in self.function.scope_variables            
        for f, condition in self.function.args:
            _domain = (Complement(universalSat, union)) & x.domain_conditioned(condition) & domain
            assert not _domain or _domain.is_integer
            if not condition:
                union |= _domain
                assert not union or union.is_integer

            if _domain.is_FiniteSet:
                for e in _domain:
                    args.append(f.subs(x, e))
            elif _domain:
                assert _domain.is_integer
                if _domain.is_Interval:
                    args.append(self.func(f, (x, _domain.min(), _domain.max() + 1)).simplify())
                else:
                    args.append(self.func(f, (x, _domain)).simplify())

        return args
    
    def _subs_limits(self, x, domain, new, simplify=True):

        def subs(function, x, domain, new):
            _function = function._subs(x, new)
            if _function == function:
                if not function._has(x):
                    ...
                else:
                    return self
            function = _function
            
            kwargs = {}
            if self.is_Boolean:
                kwargs['equivalent'] = self
#             domain = [dom._subs(x, new) for dom in domain]
            index = self.variables.index(x)
            limits = [*self.limits]
            if 'domain' in new._assumptions:
                if len(domain) == 2:
                    dom = Interval(*domain, right_open=x.is_integer, integer=x.is_integer)
                    assert new.domain == dom
                elif domain:
                    dom = domain[0]
                    if not dom.is_set:
                        dom = new.domain_conditioned(dom)
                    assert new.domain == dom
                limits[index] = (new,)
            else:
                if len(domain) == 1:
                    domain = domain[0]
                    if domain.is_boolean:
                        domain = domain._subs(x, new)
                    limits[index] = (new, domain)
                else:
                    limits[index] = (new, *domain)
            for i in range(index):
                v, *domain = limits[i]
                domain = [dom._subs(x, new) for dom in domain]
                limits[i] = (v, *domain)

            this = self.func(function, *limits, **kwargs)
            return this.simplify() if simplify else this

        if self.function.is_ExprWithLimits and new in self.function.variables_set:
            if self.function.is_Exists:
                return self
            y = self.function.generate_free_symbol(self.function.variables_set, **new.type.dict)
            assert new != y
            function = self.function.limits_subs(new, y)
            if function == self.function:
                return self
            this = subs(function, x, domain, new)
 
            if this.is_ExprWithLimits:
                if this.function.is_ExprWithLimits and y in this.function.variables_set:
                    function = this.function.limits_subs(y, x)
                else:
                    function = this.function
     
                this = this.func(function, *this.limits)
                
            if this.is_Boolean:
                this.equivalent = self
            return this
        return subs(self.function, x, domain, new)

    def limits_subs(self, old, new, simplify=True):
        from sympy.solvers import solve
        if len(self.limits) == 1:
            limit = self.limits[0]
            x, *domain = limit

            if old == x:
                if self.function._has(new):
                    return self
                
                if not domain: 
                    if new._has(x):
                        p = new.as_poly(x)
                        if p is None or p.degree() != 1:
                            return self
                        alpha = p.coeff_monomial(x)
                        if alpha == 1:
                            diff = new - x
                            a, b = x.domain.min() - diff, x.domain.max() - diff
                            self = self.func(self.function._subs(old, new), (x, a, b))
                            return self.simplify() if simplify else self
                        elif alpha == -1:
                            return self
                        else:
                            return self
                    else:
                        domain_assumed = new.domain_assumed
                        if domain_assumed: 
                            assert domain_assumed == x.domain
                            limit = (new,)
                        else:
                            domain = x.domain
                            if domain.is_UniversalSet:
                                limit = (new,)
                            else:
                                limit = (new, domain)
                        self = self.func(self.function._subs(old, new), limit)
                        return self.simplify() if simplify else self
                if not new._has(x):
                    return self._subs_limits(x, domain, new, simplify=simplify)

            if len(domain) == 2:
                a, b = domain

            p = old.as_poly(x)

            if p is None or p.degree() != 1:
                if x.is_Slice:
                    x = x.subs(old, new)
                    self = self.func(self.function.subs(old, new), (x,))
                    return self.simplify() if simplify else self
                return self

            if new.has(x):
                diff = old - new
                if diff._has(x):
                    if old != x: 
                        return self
                    
                    function = self.function._subs(old, new)
                    if len(domain) == 2:
                        a, b = domain
                        if a.is_boolean:
                            cond, baseset = domain
                            assert baseset.is_set
                            cond = cond._subs(old, new)
                            if self.is_boolean:
                                self = self.func(function, (x, cond, baseset), equivalent=self)
                            else:
                                self = self.func(function, (x, cond, baseset))                            
                        else:                            
                            from sympy import Contains
                            cond = Contains(new, Interval(a, b, right_open=x.is_integer, integer=x.is_integer))
                            self = self.func(function, (x, cond))
                    elif len(domain) == 1:
                        cond = domain[0]
                        if cond.is_boolean:
                            cond = cond._subs(old, new)
                            if self.is_boolean:
                                self = self.func(function, (x, cond), equivalent=self)
                            else:
                                self = self.func(function, (x, cond))
                            
                    return self.simplify() if simplify else self
                    
                else: 
                    if old != x:
                        alpha = p.coeff_monomial(x)
                        diff /= alpha
                        
                    if diff.is_zero:
                        return self
                    
                    function = self.function._subs(x, x - diff)
                    if len(domain) == 2:
                        self = self.func(function, (x, a + diff, b + diff))
                    elif len(domain) == 1:
                        cond = domain[0]
                        assert cond.is_boolean
                        cond = cond._subs(x, x - diff)
                        self = self.func(function, (x, cond))
                    else:
                        self = self.func(function, (x,))
            else:
                if old != x:
                    sol = solve(old - new, x)
                    if len(sol) != 1:
                        return self
                    new = sol[0]
    
                _x = new.free_symbols - old.free_symbols
    
                if len(_x) != 1:
                    return self
                _x, *_ = _x
    
                function = self.function.subs(x, new)
    
                if domain:
                    a = solve(new - a, _x)
                    b = solve(new - b, _x)
                    if len(a) != 1 or len(b) != 1:
                        return self
                    a, b = a[0], b[0]
    
                    p = new.as_poly(_x)
                    alpha = p.coeff_monomial(_x)
                    if alpha > 0:
                        self = self.func(function, (_x, a, b))
                    elif alpha < 0:
                        self = self.func(function, (_x, b, a))
                    else:
                        return self
                else:
                    self = self.func(function, (_x))
            return self.simplify() if simplify else self

        elif len(self.limits) == 0:
            function = self.function.subs(old, new)

            return self.func(function, *self.limits)
        else: 
            
            if new in self.variables_set:
                d = Dummy(**new.type.dict)
                this = self.limits_subs(old, d)
                this = this.limits_subs(new, old)                
                return this.limits_subs(d, new)
            
            limits = [*self.limits]
            variables = self.variables
            hit = False
            for i, limit in enumerate(limits):
                x, *domain = limit
                if old == x and not new.has(x):
                    return self._subs_limits(x, domain, new)

                if len(domain) == 2:
                    a, b = domain

                p = old.as_poly(x)
                if p is None or p.degree() == 0:
                    continue
                if p.degree() != 1:
                    return self

                if new.has(x):
                    diff = old - new
                    if old != x:
                        if diff.has(x):
                            return self

                        alpha = p.coeff_monomial(x)
                        diff /= alpha

                    function = self.function.subs(x, x - diff)
                    
                    if diff.has(*variables[:i]):
                        return self
                    if domain:
                        limits[i] = (x, a + diff, b + diff)
                    for j in range(i):
                        var, *ab = limits[j]
                        if ab:
                            ab = [e._subs(x, x - diff) for e in ab]
                            limits[j] = (var, *ab)
                    hit = True
                break

            if not hit:
                return self.func(self.function.subs(old, new), *self.limits)
            
            return self.func(function, *limits)

        return self
    
#     Override this stub if you want to do anything more than
#     attempt a replacement of old with new in the arguments of self.
    def _subs_utility(self, old, new, **hints):
        if old.is_symbol and not self.function._has(old):
            if not any(limit._has(old) for limit in self.limits):
                return self
            
            hit = False
            limits = [*self.limits]
             
            for i, limit in enumerate(self.limits):
                _limit = limit._subs_limits(old, new)
                if _limit != limit:
                    limits[i] = _limit
                    hit = True
            if hit:
                self = self.func(self.function, *limits).simplify()
            return self
            
        intersect = {x for x in new.free_symbols & self.variables_set - old.free_symbols if not old._has(x)}            
        if intersect: 
            this = self
            excludes = self.variables_set | new.free_symbols
            for var in intersect:
                _var = self.generate_free_symbol(excludes, integer=True)
                this = this.limits_subs(var, _var)
                excludes.add(_var) 
            _this = this._subs(old, new)
            if _this == this:
                return self
            return _this
        
        from sympy.core.basic import _aresame
        if self == old or _aresame(self, old) or self.dummy_eq(old): 
            return new

        if old in self.variables_set:
            for i in range(len(self.limits) - 1, -1, -1):
                x = self.limits[i][0]
                if x != old:
                    continue
                
                hit = False
                limits = [*self.limits]
                for j in range(i, len(self.limits)):
                    limit = self.limits[j]
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[j] = _limit
                        hit = True                    
                if hit:
                    self = self.func(self.function, *limits)
                break
            return self
        
        if old.is_Slice:
            rule = {}
            for limit in self.limits[::-1]:
                x, *domain = limit
                if len(domain) == 2:
                    a, b = domain
                    if a.free_symbols & rule.keys():
                        a = a.subs(rule)
                    if b.free_symbols & rule.keys():
                        b = b.subs(rule)
                    rule[x] = x.copy(domain=Interval(a, b, right_open=True, integer=True))
            function = self.function
            if rule:
                function = self.function.subs(rule)

            _function = function._subs(old, new)
            if _function != function:
                if rule:
                    _function = _function.subs({v: k for k, v in rule.items()})

                return self.func(_function, *(limit._subs(old, new) for limit in self.limits))
            
    def _subs(self, old, new, **hints):
        this = self._subs_utility(old, new, **hints)
        if this is not None:
            return this
        
        if old.has(*self.variables) and not new.has(*self.variables):
            return self
        
        from sympy.core.basic import _aresame
        hit = False
        args = [*self.args]
        for i, arg in enumerate(args):
            if not hasattr(arg, '_eval_subs'):
                continue
            arg = arg._subs(old, new)    
            if not _aresame(arg, args[i]):
                hit = True
                args[i] = arg
        if hit:
            rv = self.func(*args)
            return rv
        return self

    def bisect(self, indices, wrt=None):
        kwargs = {'evaluate': False}
        if self.is_Boolean:
            kwargs['equivalent'] = self                
        
        if len(self.limits) > 1:
            if wrt is None:
                x, *ab = self.limits[-1]
                if len(ab) == 2: 
                    a, b = ab   
                    if x.is_integer: 
                        mid = Symbol.process_slice(indices, a, b + 1)
                        assert mid >= a, "mid >= a => %s" % (mid >= a)        
                        assert mid <= b + 1, "mid <= b + 1 => %s" % (mid <= b + 1)
                        
                        if mid is None:
                            return self
                        if isinstance(mid, tuple):
                            ...
                            assert False                        
                        return self.func.operator(self.func(self.function, *self.limits[:-1], (x, a, mid - 1)).simplify(), self.func(self.function, *self.limits[:-1], (x, mid, b)).simplify(), **kwargs)
                    
                return self
            
            for i, limit in enumerate(self.limits):
                x, *ab = limit 
                if x != wrt:
                    continue
                if len(ab) == 2:
                    universe = Interval(*ab, right_open=True, integer=x.is_integer)
                else:
                    universe, *_ = ab
                    
                limits1 = [*self.limits]
                limits1[i] = (x, universe & indices)
                
                limits2 = [*self.limits]
                limits2[i] = (x, universe - indices)

                return self.func.operator(self.func(self.function, *limits1).simplify(), self.func(self.function, *limits2), **kwargs)
            return self

        (x, *ab), *_ = self.limits
        if x.is_Slice:
            x, z = x.bisect(indices, allow_empty=True).args
            if not ab:
                return self.func(self.func(self.function, (x,)).simplify(), (z,))

        if not isinstance(indices, slice): 
            if len(ab) == 1:
                universe = ab[0]
            elif len(ab) == 2:
                universe = Interval(*ab, right_open=True, integer=True)
            else:
                universe = x.domain
                
            if not isinstance(indices, set) and indices.is_boolean:
                indices = x.domain_conditioned(indices)
            intersection = universe & indices
            if intersection:
                return self.func.operator(self.func(self.function, (x, intersection)).simplify(),
                                          self.func(self.function, (x, universe - indices)).simplify(), **kwargs)
            return self

        if len(ab) == 2:
            a, b = ab
            if x.is_integer:
                mid = Symbol.process_slice(indices, a, b)
                assert mid >= a, "mid >= a => %s" % (mid >= a)        
                assert mid <= b, "mid <= b => %s" % (mid <= b)
    
                if mid is None:
                    return self
                if isinstance(mid, tuple):
                    ...
                    assert False                        
                    
                lhs = self.func(self.function, (x, a, mid))                
                rhs = self.func(self.function, (x, mid, b))
                return self.func.operator(lhs.simplify(), rhs.simplify(), **kwargs)

        return self

    def _has(self, pattern):
        """Helper for .has()"""
#         from sympy.tensor.indexed import Indexed, Slice
        from sympy.core.assumptions import BasicMeta
        from sympy.core.function import UndefinedFunction
        if isinstance(pattern, (BasicMeta, UndefinedFunction)):
            return Expr._has(self, pattern)
        if not isinstance(pattern, (Symbol, Indexed, Slice)):
            return Expr._has(self, pattern)

        function = self.function
        limits = []

        if self.limits:
            for i, limit in enumerate(self.limits):
                x, *args = limit
                if x == pattern:
                    mapping = self.limits_dict
                    domain = mapping.pop(x)
                    if not isinstance(domain, list) and domain.is_set and domain._has(pattern):
                        return True
                    
                    mapping = limits_dict(self.limits[i + 1:])
                        
                    for k, domain in mapping.items():
                        if k._has(pattern) or not isinstance(domain, list) and domain.is_set and domain._has(pattern):
                            return True
                    return False

                if x.is_Slice and pattern.is_Slice and x.base == pattern.base:
                    if x.index_contains(pattern):
                        return False
                    if pattern.index_contains(x):
                        indices = []
                        for i, ((start, stop), (_start, _stop)) in enumerate(zip(x.indices, pattern.indices)):
                            if _start < start:
                                indices.append(slice(_start, start))
#                                 extreme case to consider:
#                                 if stop < _stop:                                
#                                     indices.append(slice(stop, _stop))
                            elif stop < _stop:                                
                                indices.append(slice(stop, _stop))
                            else:
                                return False
                                
                        if self._has(pattern.base[indices]):
                            return True
                    return False
                
                if (pattern.is_Slice or pattern.is_Indexed) and len(args) == 2 and args[0].is_integer:
                    assert args[1].is_integer or args[1].is_infinite, "self = %s, args = %s" % (self, args)
                    _x = x.copy(domain=Interval(*args, integer=True))
                    function = function._subs(x, _x)
                    limits.append(Tuple(_x, *args))
                else:
                    limits.append(limit)
                        
        boolean = function._has(pattern)

        return boolean or any(arg._has(pattern) for arg in limits)

    @classmethod
    def class_key(cls):
        """Nice order of classes. """
        return 6, 0, cls.__name__

    @property
    def shape(self):
        return self.function.shape

    def _eval_domain_defined(self, x, allow_empty=True): 
        if x.dtype.is_set:
            return x.universalSet            
        
        domain = x.domain        
        if x in self.variables:
            return domain
                    
        for limit in self.limits:
            var, *ab = limit
            if var.is_Slice:
                domain &= var._eval_domain_defined(x, allow_empty=allow_empty)
            else:
                domain &= var.domain_defined(x)
            for e in ab:
                domain &= e.domain_defined(x)
        
        if self.function._has(x):
            domain &= self.function.domain_defined(x)
            if x not in self.function.free_symbols:
                v = self.variable
                if not v.is_Slice:
                    v_domain = self.limits_dict[v]
                    for free_symbol in self.function.free_symbols:
                        if not free_symbol._has(v) or not free_symbol.is_Indexed:
                            continue
                        pattern = free_symbol.subs(v, Wild(v.name, **v.assumptions0))
                        res = x.match(pattern)
                        if res: 
                            t_, *_ = res.values()
                            if isinstance(v_domain, list) or t_ in v_domain:
                                function = self.function._subs(v, t_)
                                domain &= function.domain_defined(x)
                                break
            
        return domain

    def match_index(self, expr):
        if len(self.limits) != 1:
            return
        
        i, *_ = self.limits[0]
        i_ = Wild(i.name)

        dic = expr.match(self.function.subs(i, i_))
        if dic:
            return dic[i_]

    def limits_swap(self):
        if len(self.limits) == 2:
            i_limit, j_limit = self.limits
            j, *_ = j_limit
            if not i_limit._has(j):
                return self.func(self.function, j_limit, i_limit)
        return self

    def simplify(self, deep=False, **kwargs):
        limits = [*self.limits]
        dic = {x: domain for x, *domain in limits}
        updated = False
        for var, *domain in limits:
            if len(domain) == 1:
                domain = domain[0]
                if domain.is_set:
                    continue
            if not var.is_Slice:
                continue
            
            start, stop = var.index
            if var.base[stop] in dic and not dic[var.base[stop]] and not dic[var]:
                del dic[var.base[stop]]
                del dic[var]
                dic[var.base[start: stop + 1]] = ()
                updated = True
            elif var.base[start - 1] in dic and not dic[var.base[start - 1]] and not dic[var]:
                del dic[var.base[start - 1]]
                del dic[var]
                dic[var.base[start - 1: stop]] = ()
                updated = True
            elif not self.function.has(var.base[stop - 1]): 
                del dic[var]
                _var = var.base[start: stop - 1]
                if not domain._has(_var):
                    domain = ()
                dic[_var] = domain
                updated = True
            elif not self.function.has(var.base[start]):
                if not domain._has(var.base[start]):
                    del dic[var]
                    dic[var.base[start + 1: stop]] = domain
                    updated = True
            else:
                from sympy.core.basic import preorder_traversal
                validDomain = S.Zero.emptySet
                for p in preorder_traversal(self.function):
                    if p.is_Slice and p.base == var.base:
                        validDomain |= Interval(*p.indices, right_open=True, integer=True)
                    elif p.is_Indexed and p.base == var.base:
                        validDomain |= p.indices[0].set
                universe = Interval(*var.indices, right_open=True, integer=True)
                if validDomain != universe and validDomain in universe:
                    if validDomain.is_Interval:
                        start, end = validDomain.min(), validDomain.max() + 1
                        del dic[var]
                        dic[var.base[start: end]] = domain
                        updated = True

        if updated:
            dic_original = {x: domain for x, *domain in limits}
            limits = [(key, *dic[key])for key in dic.keys() - dic_original.keys()] + limits
            for key in dic_original.keys() - dic.keys():
                del limits[[x for x, *_ in limits].index(key)]

            if self.is_boolean:
                kwargs = {'equivalent': self}
            else:
                kwargs = {}
            return self.func(self.function, *limits, **kwargs)
        return self

    @classmethod
    def identity(cls, self, **assumptions):
        return cls.operator.identity.copy(**assumptions)


class AddWithLimits(ExprWithLimits):
    r"""Represents unevaluated oriented additions.
        Parent class for Integral and Sum.
    """

    is_complex = True
    
    def __new__(cls, function, *symbols, **assumptions):
        pre = _common_new(cls, function, *symbols, **assumptions)
        if type(pre) is tuple:
            function, limits, orientation = pre
        else:
            return pre
        
        if function.is_set:
            assert not limits
            if function.is_FiniteSet: 
                return Add(*function.args)
            if function.is_Interval:
                if function.is_integer:
                    a, b = function.min(), function.max()
                    return (a + b) * (b - a + 1) / 2
        else:
            function = orientation * function  # orientation not used in ExprWithLimits
            
        return Expr.__new__(cls, function, *limits, **assumptions)

    def _eval_adjoint(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.adjoint(), *self.limits)
        return None

    def _eval_conjugate(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.conjugate(), *self.limits)
        return None

    def _eval_transpose(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.function.transpose(), *self.limits)
        return None

    def _eval_factor(self, **hints):
        if 1 == len(self.limits):
            summand = self.function.factor(**hints)
            if summand.is_Mul:
                out = sift(summand.args, lambda w: not set(self.variables) & w.free_symbols)
                return Mul(*out[True]) * self.func(Mul(*out[False]), *self.limits)
        else:
            summand = self.func(self.function, *self.limits[0:-1]).factor()
            if not summand.has(self.variables[-1]):
                return self.func(1, [self.limits[-1]]).doit() * summand
            elif isinstance(summand, Mul):
                return self.func(summand, self.limits[-1]).factor()
        return self

    def _eval_expand_basic(self, **hints):
        summand = self.function.expand(**hints)
#         if summand.is_Add and summand.is_commutative:
        if summand.is_Add:
            args = []
            for arg in summand.args:
                if arg._coeff_isneg():
                    args.append(-self.func(-arg, *self.limits))
                else:
                    args.append(self.func(arg, *self.limits))
            return Add(*args)
#             return Add(*[self.func(i, *self.limits) for i in summand.args])
        elif summand.is_DenseMatrix:
            return Matrix._new(summand.rows, summand.cols, [self.func(i, *self.limits) for i in summand._mat])
        elif summand != self.function:
            if summand._coeff_isneg():
                return -self.func(-summand, *self.limits)
            return self.func(summand, *self.limits)
        
        return self

    def as_multiple_limits(self):
        if self.function.is_Mul:
            integral = []
            function = []
            for arg in self.function:
                if isinstance(arg, self.func):
                    integral.append(arg)
                else:
                    function.append(arg)
            if integral:
                limits = self.limits[:]
                for it in integral:
                    limits += it.limits
                    if isinstance(it.function, Mul):
                        function += it.function.args
                    else:
                        function.append(it.function)
                return self.func(Mul(*function), *limits)
        return self

    def as_separate_limits(self):
        if len(self.limits) < 2:
            return self
        limit = self.limits[0]
        x, a, b = limit

        limits = []
        for i in range(1, len(self.limits)):
            t, *domain = self.limits[i]
            if domain:
                domain = Interval(*domain, right_open=t.is_integer, integer=t.is_integer)
            else:
                domain = Interval(-S.oo, S.oo, integer=t.is_integer)

            if a._has(t):
                domain &= t.domain_conditioned(a <= x)
                a = MIN(a, self.limits[i]).doit()
            if b._has(t):
                if t.is_integer:
                    domain &= t.domain_conditioned(x < b)
                else:
                    domain &= t.domain_conditioned(x <= b)
                b = MAX(b, self.limits[i]).doit()

            if t.is_integer:
                limit = (t, domain.min(), domain.max() + 1)
            else:
                limit = (t, domain.start, domain.stop)
            limits.append(limit)

        function = self.func(self.function, *limits).simplify()
        return self.func(function, (x, a, b))

    def _eval_is_extended_real(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
                
        return function.is_extended_real
    
    def _eval_is_extended_positive(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
        return function.is_extended_positive

    def _eval_is_extended_negative(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
                    
        return function.is_extended_negative

    @classmethod
    def rewrite_from_Plus(cls, self):
        function = []
        limits = None        
        for arg in self.args:
            if isinstance(arg, cls):
                function.append(arg.function)
                if limits is None:
                    limits = arg.limits
                else:
                    if limits != arg.limits:
                        return self
                continue

            additive = arg.astype(cls)
            if additive is None:
                return self
            else:
                if limits is None:
                    limits = additive.limits
                else:
                    if limits != additive.limits:
                        if self.func(*function, additive.function).is_zero:
                            limits_complemented = limits_complement(limits, additive.limits)
                            if limits_complemented is not None:
                                limits = limits_complemented
                                continue
                        
                        return self

                function.append(additive.function)

        return cls(self.func(*function), *limits)

    @classmethod
    def rewrite_from_Times(cls, self):
        for i, sgm in enumerate(self.args):
            if isinstance(sgm, cls):
                args = [*self.args]
                args[i] = S.One
                variables_set = sgm.variables_set
                duplicate_set = set()
                for a in args:
                    duplicates = {v for v in variables_set if a._has(v)}
                    if duplicates:
                        variables_set -= duplicates
                        duplicate_set |= duplicates
                
                if duplicate_set:
                    excludes = set()
                    for v in duplicate_set:
                        _v = self.generate_free_symbol(excludes=excludes, **v.type.dict)
                        sgm = sgm.limits_subs(v, _v)
                        excludes.add(_v)                        
                        
                args[i] = sgm.function
                function = self.func(*args).powsimp()
                return cls(function, *sgm.limits)
        return self

    @classmethod
    def rewrite_from_MatMul(cls, self):
        for i, arg in enumerate(self.args):
            if isinstance(arg, cls):
                args = [*self.args]
                args[i] = arg.function 
                function = self.func(*args).powsimp()
                return cls(function, *arg.limits)
        return self


class MINMAXBase(ExprWithLimits):
    
    is_extended_real = True
    
    @property
    def shape(self):
        if self.limits:
            return self.function.shape
        return self.function.shape[:-1]
    
    def _eval_is_finite(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite
    
    def simplify(self, deep=False, **kwargs):
        if not self.limits:
            if self.function.is_LAMBDA:
                if len(self.function.limits) == 1 and not self.function.variable.shape:
                    function = self.function.function
                    self = self.func(function, *self.function.limits).simplify(**kwargs)
            elif self.function.is_Piecewise:
                self = self.function.func(*((self.func(e).simplify(), c) for e, c in self.function.args)).simplify()            
            return self
        (x, *_), *_ = self.limits
        independent, dependent = self.function.as_independent(x, as_Add=True)
        if not independent.is_zero: 
            return self.func(dependent, *self.limits) + independent
        
        independent, dependent = self.function.as_independent(x, as_Add=False)
        if independent != S.One: 
            if independent.is_extended_negative:
                return self.reversed_type(dependent, *self.limits) * independent
            if independent.is_extended_positive:
                return self.func(dependent, *self.limits) * independent
            if independent._coeff_isneg():
                return -self.func.reversed_type(-self.function, *self.limits)
            
        if self.function.is_Log:
            return self.function.func(self.func(self.function.arg, *self.limits))
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def bounds(self, x, domain, cls):
        try:
            assert self.function.is_infinitesimal is None                    
            from sympy import limit
            maxi = domain.max()
            if maxi.is_infinite:
                maxi = limit(self.function, x, maxi)
#             elif maxi.is_infinitesimal:            
#                 maxi = self.function._subs(x, maxi, symbol=False)
            else:
                maxi = self.function._subs(x, maxi, symbol=False)
        
            mini = domain.min()
            if mini.is_infinite:
                mini = limit(self.function, x, mini)    
#             elif mini.is_infinitesimal:            
#                 mini = self.function._subs(x, mini, symbol=False)
            else: 
                mini = self.function._subs(x, mini, symbol=False)
            return cls(maxi, mini)
        except:
            return self
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.function))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.function))
    
    def _latex(self, p):
        name = self.__class__.__name__.lower()[:3]

        if len(self.limits) == 1: 
            tex = r"\%s\limits_{%s} " % (name, self.limits[0]._format_ineq(p))
        elif len(self.limits) == 0:
            tex = r"\%s " % name
        else:
            if all(len(limit) == 1 for limit in self.limits):
                tex = r"\%s\limits_{{%s}} " % (name, str.join(', ', [l._format_ineq(p) for l in self.limits]))
            else:
                tex = r"\%s\limits_{\substack{%s}} " % (name, str.join('\\\\', [l._format_ineq(p) for l in self.limits]))

        if isinstance(self.function, Add):
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex

    @property
    def dtype(self):
        if not self.limits:
            if self.function.is_set:
                return self.function.etype
        return self.function.dtype

    @classmethod        
    def rewrite_from_LAMBDA(cls, self):
        if isinstance(self.function, cls) and len(self.function.limits) == 0:
            minimum = self.function
            function = minimum.function
            return minimum.func(self.func(function, *self.limits).simplify())
        return self

    @classmethod        
    def rewrite_from_Log(cls, self):
        if isinstance(self.arg, cls):
            m = self.arg
            return m.func(self.func(m.function), *m.limits)        
        return self


class Minimize(MINMAXBase):
    r"""Represents unevaluated MIN operator.
    Minimize[f,x]
    minimizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Min

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if domain:
            domain = Interval(*domain, right_open=x.is_integer, integer=x.is_integer)
        else:
            domain = x.domain        
            if domain.is_CartesianSpace:
                return self
            
        if self.function.is_infinitesimal is not None:
            function, epsilon = self.function.clear_infinitesimal()
            return self.func(function, *self.limits).doit() + epsilon
        
        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                b = p.nth(0)
                if a.is_positive:
                    return a * domain.min() + b
                elif a.is_negative:
                    return a * domain.max() + b
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_negative:
                    return self.bounds(x, domain, Min)                        
                elif a.is_positive:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.nth(0)
                        return (4 * a * c - b * b) / (4 * a)
                    return self.bounds(x, domain, Min)
            elif p.degree() <= 0:
                return self.function
        elif self.function.is_MinMaxBase:
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))

        return self
    
    def _eval_summation(self, f, x):
        return None
        
    def _eval_is_extended_negative(self):
        if not self.limits and self.function.is_set:
            if self.function.infimum().is_extended_negative:
                return True

    def _eval_is_extended_positive(self):
        if not self.limits and self.function.is_set:
            if self.function.infimum().is_extended_positive:
                return True
            
    # infimum returns the value which is bound to be below (<=) the minimum!
    def infimum(self):
        if not self.limits and self.function.is_set:
            return self.function.infimum()
        return self


MIN = Minimize

                
class Maximize(MINMAXBase):
    r"""Represents unevaluated MAX operator.
    Maximize[f,x]
    maximizes f with respect to x.
    """
    
    __slots__ = ['is_commutative']
    operator = Max

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]
        if x.is_set:
            return self
        
        if domain:
            domain = Interval(*domain, right_open=x.is_integer, integer=x.is_integer)
        else:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self

        if self.function.is_infinitesimal is not None:
            function, epsilon = self.function.clear_infinitesimal()
            return self.func(function, *self.limits).doit() + epsilon
        
        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)       
                b = p.nth(0)         
                if a.is_extended_positive:
                    return a * domain.max() + b
                elif a.is_extended_negative:
                    return a * domain.min() + b                        
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_positive:
                    return self.bounds(x, domain, Max)
                elif a.is_negative:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.nth(0)
                        return (4 * a * c - b * b) / (4 * a)
                    return self.bounds(x, domain, Max)
            elif p.degree() <= 0:
                return self.function
        elif self.function.is_MinMaxBase:
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))
                
        return self
    
    def separate(self):
        (x, *_), *_ = self.limits
        if x.is_Slice:
            z, x = x.pop()
            return self.func(self.func(self.function, (x,)).simplify(), (z,))
        return self

    # supremum returns the value which is bound to be above (>=) the minimum!
    def supremum(self):
        if not self.limits and self.function.is_set:
            return self.function.supremum()
        return self

    def _eval_is_extended_positive(self):
        if not self.limits and self.function.is_set:
            if self.function.supremum().is_extended_positive:
                return True

    def _eval_is_extended_negative(self):
        if not self.limits and self.function.is_set:
            if self.function.supremum().is_extended_negative:
                return True


MAX = Maximize

MAX.reversed_type = MIN
MIN.reversed_type = MAX


class ArgMinMaxBase(ExprWithLimits):

    @property
    def shape(self):
        shape = None
        for x, *_ in self.limits:
            x_shape = x.shape
            if shape is None:
                shape = x_shape
                continue
            if x_shape == shape:
                shape = (2, *shape)                
                continue            
            assert x_shape == shape[1:], 'illegal shape %s' % x_shape
            shape = (shape[0] + 1, *x_shape)
                
        return shape
    
    def _eval_is_complex(self):
        return fuzzy_and(x.is_complex for x, *_ in self.limits)
    
    def simplify(self, deep=False, **kwargs):
        if not self.limits:
            if self.function.is_LAMBDA:
                if len(self.function.limits) == 1 and not self.function.variable.shape:
                    function = self.function.function                    
                    return self.func(function, *self.function.limits).simplify(**kwargs)
            return self
        * _, (x, *_) = self.limits
        independent, dependent = self.function.as_independent(x, as_Add=True)
        if not independent.is_zero: 
            return self.func(dependent, *self.limits)
        
        independent, dependent = self.function.as_independent(x, as_Add=False)
        if independent != S.One:
            if independent.is_extended_positive: 
                return self.func(dependent, *self.limits)
            if independent.is_extended_negative: 
                return self.reversed_type(dependent, *self.limits)            

        if self.function._coeff_isneg():
            return self.func.reversed_type(-self.function, *self.limits)
        if self.function.is_Log:
            return self.func(self.function.arg, *self.limits)
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.function))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.function))
    
    def _latex(self, p):
        name = self.__class__.__name__.lower()[3:6]
        name = r'\mathop{{\rm %s}^{-1}}' % name
        if len(self.limits) == 1:
            tex = r"%s\limits_{\substack{%s}} " % (name, self.limits[0]._format_ineq(p))
        else:
            if all(len(limit) == 1 for limit in self.limits):
                tex = r"%s\limits_{{%s}} " % (name, str.join(', ', [l._format_ineq(p) for l in self.limits]))
            else:
                tex = r"%s\limits_{\substack{%s}} " % (name, str.join('\\\\', [l._format_ineq(p) for l in self.limits]))

        if isinstance(self.function, Add):
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex


class ArgMin(ArgMinMaxBase):
    r"""Represents unevaluated argmin operator.
    Minimize[f,x]
    minimizes f with respect to x.
    """

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        ...
        
    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if domain:
            domain = Interval(*domain, right_open=x.is_integer, integer=x.is_integer)
        else:
            domain = x.domain        
            if domain.is_CartesianSpace:
                return self
        assert self.function.is_infinitesimal is None
        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_extended_positive:
                    return domain.min()
                elif a.is_extended_negative:
                    return domain.max()
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_negative:
                    return self.bounds(x, domain, Min)
                elif a.is_positive:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.nth(0)
                        delta = 4 * a * c - b * b
                        from sympy import sqrt
                        return (-b + sqrt(delta)) / (2 * a)
                    return self.bounds(x, domain, Min)
            elif p.degree() <= 0:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
        elif self.function.is_MinMaxBase:
            print('warning, unreliable implementation')
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))

        return self
    
    def _eval_is_extended_negative(self):
        ...

    def _eval_is_extended_positive(self):
        ...
            
            
class ArgMax(ArgMinMaxBase):
    r"""Represents unevaluated argmax operator.
    Maximize[f,x]
    maximizes f with respect to x.
    """

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        ...

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]

        if domain:
            domain = Interval(*domain, right_open=x.is_integer, integer=x.is_integer)
        else:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self

        p = self.function.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_extended_positive:
                    return domain.max()
                elif a.is_extended_negative:
                    return domain.min()
            elif p.degree() == 2:
                a = p.coeff_monomial(x * x)
                if a.is_positive:
                    return self.bounds(x, domain, Max)
                elif a.is_negative:
                    b = p.coeff_monomial(x)
                    zero_point = -b / (2 * a)
                    if zero_point in domain:
                        c = p.nth(0)
                        delta = 4 * a * c - b * b
                        from sympy import sqrt
                        return (-b + sqrt(delta)) / (2 * a)
                    return self.bounds(x, domain, Max)
            elif p.degree() <= 0:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
        elif self.function.is_MinMaxBase:
            print('error, unreliable implementation')
            return self.function.func(*(self.func(arg, *self.limits).doit() for arg in self.function.args))
                
        return self
    
    def _eval_is_extended_positive(self):
        ...

    def _eval_is_extended_negative(self):
        ...


ArgMax.reversed_type = ArgMin
ArgMin.reversed_type = ArgMax


class LAMBDA(ExprWithLimits):
    r"""Represents unevaluated LAMBDA operator.
    """
    
    operator = BlockMatrix
    
    def __new__(cls, function, *symbols, **assumptions):
        symbols = list(symbols)

        for i, limit in enumerate(symbols):
            if isinstance(limit, tuple) and len(limit) > 1:
                x, *domain = limit
                if 'domain' in x._assumptions:
#                     local variable
                    if len(domain) == 2:
                        if x.domain == Interval(*domain, integer=x.is_integer):
                            symbols[i] = (x,)
                            continue
                    _x = Symbol(x.name, integer=True)
                    symbols[i] = (_x, *domain)

                    function = function.subs(x, _x)
                if len(domain) == 1:
                    domain, *_ = domain
                    assert domain.is_Interval and domain.is_integer
                    mini = domain.min()
                    symbols[i] = (x, 0, domain.max() - mini + 1)
                    if mini != S.Zero:
                        function = function._subs(x, x + mini)

        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def _eval_is_zero(self):
        # a Sum is only zero if its function is zero or if all terms
        # cancel out. This only answers whether the summand is zero; if
        # not then None is returned since we don't analyze whether all
        # terms cancel out.
        if self.function.is_zero:
            return True

    def doit(self, deep=False, **hints):
        limit = self.limits[-1]
        x, a, b = limit
        diff = b - a
        if not diff.is_Number:
            return self
        
        limits = self.limits[:-1]
        if limits:
            function = self.func(self.function, *limits).doit(**hints)
        else:
            function = self.function
                    
        if deep:
            function = function.doit(deep=deep)
            
        array = []
        for i in range(diff):
            array.append(function._subs(x, sympify(i)))
        return BlockMatrix(*array)

    def as_coeff_mmul(self):
        return 1, self

    def squeeze(self):
        if not self.function._has(self.variables[-1]):
            limits = self.limits[:-1]
            if limits:
                return self.func(self.function, *limits).squeeze()
            return self.function            
        return self
    
    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a LAMBDA object!
        """
        if rhs.is_LAMBDA:
            if lhs.limits == rhs.limits:
                from sympy import ForAll
                return ForAll(self.func(lhs.function, rhs.function), *lhs.limits, equivalent=self).simplify()        

    def simplify(self, deep=False, squeeze=False, **kwargs):
        from sympy import Contains
        limits_dict = self.limits_dict
        if deep:
            function = self.function
            reps = {}
            for x, domain in limits_dict.items():
                if domain.is_set and domain.is_integer:
                    _x = x.copy(domain=domain)
                    function = function._subs(x, _x)                  
                    if 'wrt' in kwargs:
                        function = function.simplify(deep=True, **kwargs)                        
                    else:
                        function = function.simplify(deep=True, wrt=_x, **kwargs)
                    
                    reps[_x] = x
            if reps:
                for _x, x in reps.items():
                    function = function._subs(_x, x)
                if function != self.function:
                    return self.func(function, *self.limits).simplify(squeeze=squeeze)
            
        if self.function.is_LAMBDA:
            return self.func(self.function.function, *self.limits + self.function.limits).simplify(squeeze=squeeze)
        
        if self.function.is_Piecewise:
            if len(limits_dict) > 1:
                function = self.func(self.function, self.limits[0]).simplify(squeeze=squeeze)
                if not function.is_LAMBDA:
                    return self.func(function, *self.limits[1:]).simplify(squeeze=squeeze)
            else:
                if len(self.function.args) == 2:
                    e0, c0 = self.function.args[0]
                    if c0.is_Contains:
                        e, s = c0.args
                        if e in limits_dict.keys():
                            if s.is_Complement:
                                U, A = s.args
                                domain, *_ = limits_dict.values()
                                if domain in U:
                                    e1, _ = self.function.args[1]
                                    function = self.function.func((e1, Contains(e, A)), (e0, True)).simplify()
                                    return self.func(function, *self.limits).simplify(squeeze=squeeze)
                            elif s.is_Interval:
                                if limits_dict[e] in s:
                                    return self.func(e0, *self.limits).simplify(squeeze=squeeze)
                if self.function.is_set:
                    return self
                
                constant = None
                args = []
                for e, c in self.function.args:
                    if not e._has(self.variable):
                        return self
                    
                    if c._has(self.variable):
                        return self
                    
                    first, second = self.simplify_Plus(e)
                    if first is None:
                        return self
                    if constant is None:
                        constant = second
                    else:
                        if constant != second:
                            return self
                    args.append((first, c))
                this = self.function.func(*args)
                if second is not None:
                    this += self.func(second, *self.limits).simplify(squeeze=squeeze)
                return this
                    
        from sympy import Transpose
        from sympy.matrices.expressions.matmul import MatMul
        
        if self.function.is_set:
            independent, dependent = self.simplify_Set(self.function)
            if independent is not None:
                return independent
            return self
        from sympy.concrete import summations
#         from sympy.matrices.expressions.hadamard import HadamardProduct
        if isinstance(self.function, summations.Sum) and not self.function.limits and isinstance(self.function.function, Mul):
            (x, *_), *_ = self.limits
            independent, dependent = [], []
            for arg in self.function.function.args:
                if arg.has(x):
                    dependent.append(arg)
                else:
                    independent.append(arg)

            if not dependent:
                return Mul(*independent)
            if not independent:
                return self

            dependent = Mul(*dependent)
            dependent = self.func(dependent, *self.limits)
            dependent = dependent.simplify()
            dependent = Transpose(dependent)
            dependent = dependent.simplify()

            independent = Mul(*independent)
            return MatMul(independent, dependent)

        if self.function.is_Derivative:
            x, n = self.function.variable_count[0]
            order = 0
            for i, (_i, *_) in zip(x.indices[::-1], self.limits[::-1]):
                if i == _i:
                    order += 1
                    continue
                else:
                    break
            
            x = x.base[x.indices[:-order]]            
            function = Expr.__new__(self.function.func, self.function.expr, (x, n))
            limits = self.limits[:-order]
            if limits:
                return self.func(function, *limits)
            return function

        for i, limit in enumerate(self.limits):
            x, *ab = limit
            if ab:
                a, b = ab
                if a == b:
                    function = self.function._subs(x, a)                    
                    limits = [*self.limits]
                    del limits[i]
                    if limits:
                        return self.func(function, *limits).simplify()
                    return function
                if not a.is_zero: 
                    function = self.function._subs(x, x + a)
                    limits = [*self.limits]
                    limits[i] = (x, 0, b - a)
                    return self.func(function, *limits).simplify()
        
        if len(self.limits) > 1:
            this = self.func(self.function, self.limits[0])
            this_simplified = this.simplify()
            if this == this_simplified:
                return self
            return self.func(this_simplified, *self.limits[1:]).simplify(squeeze=squeeze)
        
        first, second = self.simplify_Plus(self.function)
        if first is None:
            first, second = self.simplify_Times(self.function)
            if first is None:
                if self.function.is_Exp:
                    simplified = self.func(self.function.args[0], *self.limits).simplify()
                    if not isinstance(simplified, LAMBDA):
                        return self.function.func(simplified)
                    
                if squeeze:
                    return self.squeeze()
                
                dependent, independent = self.simplify_MatMul(self.function)
                if dependent is None: 
                    return independent
                
                if independent is None: 
                    return self
                
                return MatMul(self.func(dependent, *self.limits).simplify(), independent)
            
            if second is None:
                return first

            return Mul(first, self.func(second, *self.limits).simplify(squeeze=True))

        if second is None:
            if squeeze or first.shape == self.shape:
                return first
            if first.is_zero:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
            if first.is_Number:
                from sympy import OneMatrix
                return OneMatrix(*self.shape) * first            
            return self
        return first + self.func(second, *self.limits).simplify(squeeze=squeeze)

    def simplify_Indexed(self, expr):
        variables = tuple(x for x, *_ in self.limits[::-1])        
        if len(variables) == 1:
            var = variables[0]
            index = expr.args[-1]
            if index == var:
                _, *ab = self.limits[0]
                if ab:
                    indexed = expr.base[expr.indices[:-1]]
                    zero, b = ab
                    assert zero.is_zero
                    shape = b
                    if expr.base.shape[0] != shape:
                        return indexed[:shape], None
                    return indexed, None                        
            else:
                h = index - var
                if not h._has(var):
                    _, *ab = self.limits[0]
                    if ab:
                        zero, b = ab
                        assert zero.is_zero
                        shape = b
                        return expr.base[expr.indices[:-1]][h:shape + h], None
            
        if expr.args[-len(variables):] == variables:
            return expr.base[expr.indices[:-len(variables)]], None

        return None, expr
        
    def simplify_Plus(self, expr):
        from sympy.core.basic import Atom
        variables = tuple(x for x, *_ in self.limits[::-1])
        if isinstance(expr, Atom):
            if expr in variables:
                return None, expr
            return expr, None

        if isinstance(expr, Indexed):
            return self.simplify_Indexed(expr)

        if isinstance(expr, Add):
            argsNonSimplified = []
            argsSimplified = []
            for arg in expr.args:
                simplified, nonSimplified = self.simplify_Plus(arg)
                if simplified is not None:
                    argsSimplified.append(simplified)
                if nonSimplified is not None:
                    argsNonSimplified.append(nonSimplified)

            if not argsSimplified:
                argsSimplified = None
            elif len(argsSimplified) == 1:
                argsSimplified = argsSimplified[0]
            else:
                argsSimplified = Add(*argsSimplified)

            if not argsNonSimplified:
                argsNonSimplified = None
            elif len(argsNonSimplified) == 1:
                argsNonSimplified = argsNonSimplified[0]
            else:
                argsNonSimplified = Add(*argsNonSimplified)

            return argsSimplified, argsNonSimplified

        independent, dependent = expr.as_independent(*variables, as_Add=True)
        if independent == S.Zero:
            return None, dependent
        if dependent == S.Zero:
            dependent = None
        return independent, dependent

    def simplify_Set(self, exp):
        from sympy.core.basic import Atom
        
        x = tuple(x for x, *_ in self.limits)
        if isinstance(exp, Atom):
            return exp, None

        if isinstance(exp, Indexed):
            if exp.args[-len(x):] == tuple(x for x, *_ in self.limits):
                base = exp.base[exp.indices[:-len(x)]]
                for x, *ab in self.limits:
                    if len(ab) == 1:
                        return None, exp
                    if len(ab) == 2:
                        a, b = ab
                        base = base[a:b]
                    else:
                        domain = x.domain
                        if domain == Interval(0, base.shape[0] - 1, integer=True):
                            ...
                        else:
                            return None, exp
                return base, None

        return None, exp

    def simplify_Times(self, expr):
        x, *ab = self.limits[0]

        from sympy.core.basic import Atom
        if isinstance(expr, Atom):
            if expr in self.variables_set:
                return None, expr
            return expr, None

        if expr.is_Indexed:
            return self.simplify_Indexed(expr)
            if expr.args[-1] == x:
                if not ab:
                    return expr.base[expr.indices[:-1]], None
                else:
                    a, b = ab
                    return expr.base[expr.indices[:-1]][:b], None

            return None, expr
        
        if expr.is_Times:
            argsNonSimplified = []
            argsSimplified = []
            for arg in expr.args:
                simplified, nonSimplified = self.simplify_Times(arg)
                if simplified is not None:
                    argsSimplified.append(simplified)
                if nonSimplified is not None:
                    argsNonSimplified.append(nonSimplified)

            if not argsSimplified:
                argsSimplified = None
            elif len(argsSimplified) == 1:
                argsSimplified = argsSimplified[0]
            else:
                argsSimplified = expr.func(*argsSimplified)

            if not argsNonSimplified:
                argsNonSimplified = None
            elif len(argsNonSimplified) == 1:
                argsNonSimplified = argsNonSimplified[0]
            else:
                argsNonSimplified = expr.func(*argsNonSimplified)

            return argsSimplified, argsNonSimplified

        if expr.is_Exp:
            if expr.arg.is_Indexed:
                simplified, nonSimplified = self.simplify_Times(expr.arg)
                if nonSimplified is None:
                    return expr.func(simplified), None            
                return None, expr
            
        independent, dependent = expr.as_independent(x, as_Add=False)
        if independent == S.One:
            return None, dependent
        if dependent == S.One:
            dependent = None
        return independent, dependent

    def simplify_MatMul(self, expr):
        if expr.is_MatMul:
            last = self.func(expr.args[-1], self.limits[0])
            _last = last.simplify()
            if last != _last:
                independent = expr.func(*expr.args[:-1], _last).simplify()
                limits = self.limits[1:]
                if limits:
                    independent = self.func(independent, *limits)
                return None, independent
            
            first = self.func(expr.args[0], self.limits[-1])
            _first = first.simplify()
            if first != _first:
                independent = expr.func(_first, *expr.args[1:]).simplify()
                limits = self.limits[:-1]
                if limits:
                    independent = self.func(independent, *limits)
                return None, independent

            index_simplified = None
            for i, arg in enumerate(expr.args):
                _, simplified = self.simplify_MatMul(arg)                
                if simplified is not None:
                    index_simplified = i 
                    break

            if index_simplified is None:
                return expr, None
            if index_simplified == 0:
                return None, expr
            
            return expr.func(*expr.args[:index_simplified]), expr.func(*expr.args[index_simplified:])
        
        if len(self.shape) < 2:
            return expr, None                
        
        independent, dependent = expr.as_independent(*self.variables, as_Add=False)
        if independent == S.One:
            return dependent, None 
        if dependent == S.One:
            dependent = None
        return dependent, independent 

    def __getitem__(self, indices, **_):
        function = self.function
        if isinstance(indices, (tuple, list)):
            variables_set = self.variables_set
            reps = {}            
            for (x, *domain), index in zip(self.limits[::-1], indices):
                index = sympify(index)
                variables_set.remove(x)
                if x == index:
                    continue

                for v in variables_set:
                    if not index._has(v):
                        continue
                    _v = Dummy(domain=v.domain_assumed, **v.type.dict)
                    _index = index._subs(v, _v)
                    if _index == index:
# if the substitution fails, it means that index has v only in its domain, not in its definition or explicit expression, 
# like i = Symbol.i(domain = Interval(j, oo)), where i has j, but only in its domain, not in its definition                        
                        continue
                    index = _index
                    reps[_v] = v
                    assert not index._has(v)
                    
                function = function._subs(x, index)  # .simplify() will result in prolonged process
                if not index._has(x): 
                    if function._has(x):
                        for var in postorder_traversal(function):
                            if var._has(x):
                                break
                        function = function._subs(var, var.definition)
                        function = function._subs(x, index)
                    assert not function._has(x)

            if len(indices) > len(self.limits):
                function = function[indices[len(self.limits):]]
            elif len(indices) < len(self.limits): 
                if function.is_zero:
                    shape = self.shape[len(indices):]
                    from sympy import ZeroMatrix
                    return ZeroMatrix(*shape)
                limits = self.limits[:-len(indices)]
                function = self.func(function, *limits)
                
            for k, v in reps.items():
                function = function._subs(k, v)
                    
            return function  # .simplify() will result in prolonged process
        if isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0
            x, *domain = self.limits[-1]
            if len(domain) == 2:
                n = domain[1]
            else:
                n = S.Infinity

            if start > 0:
                function = function.subs(x, x + start)
                stop -= start

                if stop >= n:
                    stop = n
            else:
                if stop >= n:
                    return self
                
            limits = [*self.limits]            
            limits[-1] = x, 0, stop
            return self.func(function, *limits)

        * limits, (x, *_) = self.limits
        if x != indices:
            function = function._subs(x, indices)
            if not indices._has(x) and function._has(x):
                for var in postorder_traversal(function):
                    if var._has(x):
                        break
                function = function._subs(var, var.definition)
                function = function._subs(x, indices)
                assert not function._has(x)
        if limits:
            return self.func(function, *limits)
        return function

    @property
    def dtype(self):
        return self.function.dtype
    
    @property
    def limits_shape(self):
        shape = []
        for x, *ab in self.limits:
            if not ab:
                domain = self.function.domain_defined(x)
                shape.append(domain.size)
            else:
                a, b = ab
                shape.append(b - a)
        shape.reverse()
        return tuple(shape)
        
    @property
    def shape(self):
        return self.limits_shape + self.function.shape

    @property
    def cols(self):
        return self.shape[-1]

    @property
    def rows(self):
        if len(self.shape) == 1:
            return 1
        return self.shape[-2]

    @property
    def is_Matrix(self):
        return len(self.shape) == 2

    @property
    def is_square(self):
        return self.rows == self.cols

    def inverse(self):
        from sympy.matrices.expressions.inverse import Inverse
        return Inverse(self)

    def _eval_determinant(self):
        from sympy.concrete.products import Product
        if not self.is_square:
            return
        if self.is_upper or self.is_lower:
            i, *domain = self.limits[0]
            if len(domain) == 2:
                a, b = domain
            else:
                if not domain:
                    domain = i.domain
                elif len(domain) == 1:
                    domain = domain[0]
                assert domain.is_Interval and domain.is_integer
                a, b = domain.min(), domain.max() + 1

            return Product[i:a:b](self[i, i]).doit()

    @property
    def is_lower(self):
        """Check if matrix is a lower triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_lower
        True

        >>> m = Matrix(4, 3, [0, 0, 0, 2, 0, 0, 1, 4 , 0, 6, 6, 5])
        >>> m
        Matrix([
        [0, 0, 0],
        [2, 0, 0],
        [1, 4, 0],
        [6, 6, 5]])
        >>> m.is_lower
        True

        >>> from sympy.abc import x, y
        >>> m = Matrix(2, 2, [x**2 + y, y**2 + x, 0, x + y])
        >>> m
        Matrix([
        [x**2 + y, x + y**2],
        [       0,    x + y]])
        >>> m.is_lower
        False

        See Also
        ========

        is_upper
        is_diagonal
        is_lower_hessenberg
        """
        j = self.generate_free_symbol(domain=Interval(0, self.cols, right_open=True, integer=True))
        i = j.generate_free_symbol(domain=Interval(0, j, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True

        i = self.generate_free_symbol(domain=Interval(0, self.rows, right_open=True, integer=True))
        j = i.generate_free_symbol(domain=Interval(i, self.cols, left_open=True, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True

    @property
    def is_upper(self):
        """Check if matrix is an upper triangular matrix. True can be returned
        even if the matrix is not square.

        Examples
        ========

        >>> from sympy import Matrix
        >>> m = Matrix(2, 2, [1, 0, 0, 1])
        >>> m
        Matrix([
        [1, 0],
        [0, 1]])
        >>> m.is_upper
        True

        >>> m = Matrix(4, 3, [5, 1, 9, 0, 4 , 6, 0, 0, 5, 0, 0, 0])
        >>> m
        Matrix([
        [5, 1, 9],
        [0, 4, 6],
        [0, 0, 5],
        [0, 0, 0]])
        >>> m.is_upper
        True

        >>> m = Matrix(2, 3, [4, 2, 5, 6, 1, 1])
        >>> m
        Matrix([
        [4, 2, 5],
        [6, 1, 1]])
        >>> m.is_upper
        False

        See Also
        ========

        is_lower
        is_diagonal
        is_upper_hessenberg
        """
        
        j = self.generate_free_symbol(domain=Interval(0, self.cols, right_open=True, integer=True))
        i = j.generate_free_symbol(domain=Interval(j + 1, self.rows, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True
        
        i = self.generate_free_symbol(domain=Interval(0, self.rows, right_open=True, integer=True))
        j = i.generate_free_symbol(domain=Interval(0, i, right_open=True, integer=True))
        if self[i, j].is_zero:
            return True

    def _latex(self, p):
        args = []
        for limit in self.limits:
            if len(limit) == 1:
                args.append(p._print(limit[0]))
#             elif len(limit) == 2:
#                 args.append(r"%s:%s" % (p._print(limit[0]), p._print(limit[1])))
            elif len(limit) == 3:
                if limit[1] == 0:
                    args.append(r"%s:%s" % (p._print(limit[0]), p._print(limit[2])))
                else:
                    args.append(r"%s:%s:%s" % (p._print(limit[1]), p._print(limit[0]), p._print(limit[2])))

        tex = r"[%s]" % ','.join(args)

        from sympy import MatMul
        if isinstance(self.function, (Add, Mul, MatMul)):
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        return '[%s](%s)' % (limits, p._print(self.function))

    def _eval_is_finite(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite

    def _eval_is_extended_real(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_real

    def _eval_is_complex(self):
        return self.function.is_complex

    def _eval_is_extended_positive(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_positive

    def _eval_is_extended_negative(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_negative
    
    def _eval_transpose(self):
        if len(self.shape) < 2:
            return self
        if len(self.function.shape) >= 2:
            return self.func(self.function.T, *self.limits)
        if len(self.function.shape) == 1:
            return 
        limits = [*self.limits]
        limits[-1], limits[-2] = limits[-2], limits[-1]
        return self.func(self.function, *limits).simplify()

    def generate_int_limit(self, index=-1, excludes=None, generator=None, free_symbol=None):
        if self.function.shape:
            len_shape = len(self.function.shape)
            if index < 0:
                index = len(self.shape) + index
            if index < len_shape:
                return self.function.generate_int_limit(index, excludes=excludes, generator=generator, free_symbol=free_symbol)
            index -= len_shape
        limit = self.limits[index]
        if excludes:
            x, *ab = limit
            if x in excludes:
                kwargs = x.type.dict
                if not ab:
                    ab = x.domain.min(), x.domain.max() + 1
                if free_symbol is not None and free_symbol not in excludes:
                    x = free_symbol
                else:
                    x = generator.generate_free_symbol(excludes, **kwargs)
                return (x, *ab)
        return limit
        
    def limits_swap(self):
        return self

    @classmethod
    def rewrite_from_Maximize(cls, self):
        *limits, limit = self.limits
        if limits:
            return self.func(cls(self.func(self.function, *limits), limit).simplify())
        return self.func(cls(self.function, limit).simplify())

    @classmethod
    def rewrite_from_Sum(cls, self):
        limits = self.limits[1:]
        sigmar = self.func(cls(self.function, self.limits[0]).simplify())
        if not limits:
            return sigmar
        return self.func(sigmar, *limits)            

    @classmethod
    def rewrite_from_Exp(cls, self):
        if self.shape:
            k = []
            for size in self.shape: 
                k.append(self.generate_free_symbol(excludes={*k}, domain=Interval(0, size - 1, integer=True)))
            return cls(self[k], *k)
        return self 
        
    @classmethod
    def rewrite_from_Swap(cls, self):
        i = self.generate_free_symbol(integer=True)
        j = self.generate_free_symbol({i}, integer=True)
        return LAMBDA[j:self.n, i:self.n](self._entry(i, j))
        
    @classmethod
    def rewrite_from_Slice(cls, self):
        size = self.shape[0]                     
        k = self.generate_free_symbol(integer=True)
        return cls[k:size](self[k])

    @classmethod
    def rewrite_from_Plus(cls, self):
        for i, lamda in enumerate(self.args):
            if isinstance(lamda, cls):
                k = lamda.variable
                args = [*self.args]
                del args[i]
                rest = self.func(*args)                
                return cls(rest[k] + lamda.function, *lamda.limits)
        return self
    
    def _eval_domain_defined(self, x):
        return ExprWithLimits._eval_domain_defined(self, x, allow_empty=False)        

    def domain_definition(self):
        eqs = []
        for x, *ab in self.limits:
            if ab:
                a, b = ab
                eqs.append(a <= b)
        return And(*eqs)

                
class UNION(Set, ExprWithLimits):
    """
    Represents a union of sets as a :class:`Set`.

    Examples
    ========

    >>> from sympy import Union, Interval
    >>> Union(Interval(1, 2), Interval(3, 4))
    Union(Interval(1, 2), Interval(3, 4))

    The Union constructor will always try to merge overlapping intervals,
    if possible. For example:

    >>> Union(Interval(1, 2), Interval(2, 3))
    Interval(1, 3)

    See Also
    ========

    Intersection

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Union_%28set_theory%29
    """
    
    operator = Union

    def as_image_set(self):
        try:
            if self.is_ConditionSet:
                expr, variable, base_set = self.base_set.image_set()
                from sympy import sets, Contains
                from sympy.sets.conditionset import conditionset
                condition = Contains(variable, base_set).simplify() & self.condition._subs(self.variable, expr)
                return sets.image_set(expr, variable, conditionset(variable, condition))
        except:
            ...

    @property
    def is_ConditionSet(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        x, *_ = limit
        if not isinstance(x, (Symbol, Indexed, Slice)):
            return False
        if not isinstance(self.function, FiniteSet) or len(self.function) != 1:
            return False
        element, *_ = self.function
        if element != x:
            return False
        if len(limit) <= 1:
            return False
        if len(limit) == 2:
            return True
        
        return limit[2].is_set

    def handle_finite_sets(self, unk):
        if self.is_ConditionSet:
            from sympy.sets.conditionset import conditionset                    
            return conditionset(self.variable, self.condition, self.base_set & unk)            
        else:
            match_index = self.match_index(unk)
            if match_index is not None:
                if match_index in self.limits_dict[self.variable]:
                    return unk            
            
    def intersection_sets(self, b):
        if self.is_ConditionSet:
            from sympy.sets.conditionset import conditionset
            if b.is_ConditionSet and self.variable == b.variable:
                return conditionset(self.variable, self.condition & b.condition, self.base_set & b.base_set)
            base_set = self.variable.domain & self.base_set
            if base_set in b:
                return self                
            return conditionset(self.variable, self.condition, self.base_set & b)
    
    @property
    def condition(self):
        if self.is_ConditionSet:
            return self.limits[0][1]
        
    def condition_set(self):
        if self.is_ConditionSet:
            return self
        
    @property
    def base_set(self):
        if self.is_ConditionSet:
            limit = self.limits[0]
            if len(limit) > 2:
                return limit[2]
            return limit[0].universalSet

    def doit(self, **hints):
        *limits, limit = self.limits
        i, a, b = limit
        dif = b - a
        if not dif.is_Integer:
            return self
        
        if limits:
            function = self.func(self.function, *limits)
        else:
            function = self.function
        
        return Union(*[function._subs(i, index + a) for index in range(dif)])

    def swap(self):
        if not self.function.is_UNION:
            return self
        U = self.function

        return U.func(self.func(U.function, *self.limits).simplify(), *U.limits)

    # this will change the default new operator!
    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def simplify(self, deep=False):
        if deep:
            _self = ExprWithLimits.simplify(self, deep=True)
            if _self != self:
                return _self

        if self.function.is_Intersection:
            independent = set()
            for arg in self.function.args:
                if not arg.has(*self.variables):
                    independent.add(arg)
            if independent:
                dependent = self.function._argset - independent
                function = self.function.func(*dependent)
                independent = self.function.func(*independent)
                return self.func(function, *self.limits) & independent

        if len(self.limits) != 1:
            return self
        
        if self.function.is_EmptySet:
            return self.function
        
        limit = self.limits[0]

        if len(limit) == 2:
            from sympy.core.relational import Unequality
            x, domain = limit

            if not self.function._has(x):
                emptySet = self.function.etype.emptySet
                return Piecewise((self.function, Unequality(Intersection(*self.limits_dict.values()), emptySet).simplify()), (emptySet, True)).simplify()
#                 return self.function
            
            if domain.is_FiniteSet:
                return self.finite_aggregate(x, domain)

            if domain.is_EmptySet:
                return domain

            if domain.is_Union:
                args = []
                success = False
                for dom in domain.args:
                    arg = self.func(self.function, (x, dom)).simplify()
                    args.append(arg)
                    if not arg.is_UNION or arg.function != self.function:
                        success = True
                if success:
                    return Union(*args)

            if domain.is_Interval and domain.is_integer:
                return self.func(self.function, (x, domain.min(), domain.max() + 1))

            if self.function.is_Complement:
                A, B = self.function.args
                if not B.has(*self.variables):
                    return self.func(A, *self.limits) - B

            if domain.is_Piecewise:
                tuples = []
                for e, c in domain.args: 
                    tuples.append((self.func(self.function, (x, e)).simplify(), c))    
                return domain.func(*tuples)
            if domain.is_boolean:
                if domain.is_Equal:
                    if domain.lhs == x:
                        return self.function._subs(x, domain.rhs)
                    elif domain.rhs == x:
                        return self.function._subs(x, domain.lhs)
                elif domain.is_Contains:
                    if domain.lhs == x:
                        return self.func(self.function, (x, domain.rhs))
                
            if domain.is_set:
                if not domain.is_symbol:
                    image_set = domain.image_set()
                    if image_set:
                        expr, sym, base_set = image_set
                        function = self.function._subs(x, expr)
                        return self.func(function, (sym, base_set))
                
            if self.is_ConditionSet:
                domain = self.limits[0][1]
                if domain.is_set: 
                    return domain
            return self

        if len(limit) > 2: 
            if limit[2].is_set:
                x, condition, base_set = limit
                # for condition set:
                if self.function == x.set:
                    domain = x.domain_conditioned(condition)
                    if not domain.is_ConditionSet:
                        return domain & base_set
            else:
                x, a, b = limit
                if a == b - 1:
                    return self.function._subs(x, a)
                domain = Interval(a, b, right_open=True, integer=True)
                if self.function.is_Piecewise:
                    arr = self.as_multiple_terms(x, domain)
                    arr = [arr[-1]] + arr[0:-1]
                    return reduce(lambda x, y: x | y, arr).simplify()
                if self.function.is_FiniteSet:
                    s = self.function
                    if len(s) == 1 and x == s.arg:
                        return domain
                if not self.function._has(x):
                    return self.function

        if len(limit) == 1:
            x = limit[0]
            if self.function.is_FiniteSet:
                if len(self.function) == 1:
                    element, *_ = self.function.args
                    if element == x:
                        return x.domain

        return self

    def union_sets(self, expr):
        if expr.is_Complement:
            A, B = expr.args
            if B in self:
                return self | A
        
        if expr.func == self.func:
            if self.function == expr.function:
                if self.is_ConditionSet and expr.is_ConditionSet:
                    from sympy.sets.conditionset import conditionset
                    if self.variable == expr.variable:
                        if self.base_set == expr.base_set: 
                            return conditionset(self.variable, self.condition | expr.condition, self.base_set)
                        if self.condition == expr.condition:
                            return conditionset(self.variable, self.condition, self.base_set | expr.base_set)
                else:
                    limits = self.limits_union(expr)
                    return self.func(self.function, *limits)
            else:
                finite_set = self.finite_set()
                if finite_set and finite_set.is_Slice:
                    _finite_set = expr.finite_set()
                    if _finite_set and _finite_set.is_Slice:
                        if finite_set.base == _finite_set.base:
                            start, stop = finite_set.indices
                            _start, _stop = _finite_set.indices
                            if _start == stop:
                                return UNION.construct_finite_set(finite_set.base, start, _stop, self.limits[0][0])
                            if stop == _start - 1:
                                return UNION.construct_finite_set(finite_set.base, start, _stop, self.limits[0][0]) - finite_set.base[stop].set

        if self.is_ConditionSet:
            return
        
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.function.subs(i, i_))
                if dic:
                    i_match = dic[i_]
                    if i_match >= a and i_match <= b:
                        return self

            elif len(args) == 1:
                domain = args[0]
                from sympy import Complement
                if domain.is_Complement:
                    A, B = domain.args
                    if B.is_FiniteSet:
                        deletes = set()
                        expr_set = self.etype.emptySet
                        for b in B:
                            s = self.function.subs(i, b)
                            if s == expr or s in expr:
                                deletes.add(b)
                                expr_set |= s
                                
                        if deletes:
                            deletes = FiniteSet(*deletes)
                            B = Complement(B, deletes)
                            expr = Complement(expr, expr_set)
                            if B:
                                A = Complement(A, B)
                            this = self.func(self.function, (i, A)).simplify()
                            if expr.is_EmptySet:
                                return this
                            return this | expr
                    elif B.is_Complement:
# apply: A \ (B \ C) = (A \ B) | (A & B & C)
                        b, c = B.args
                        domain = Complement(A, b)                        
#                         print(A & b & c)
                        assert Complement(A, Complement(b, c)) == Complement(A, b) | (A & b & c)
                        expr |= self.func(self.function, (i, A & b & c)).simplify()
                        return expr | self.func(self.function, (i, domain))

    def _sympystr(self, p):
        if self.is_ConditionSet: 
            return 'ConditionSet(%s)' % ', '.join(p.doprint(arg) for arg in self.limits[0])
        
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '∪[%s](%s)' % (limits, p.doprint(self.function))
        return '∪(%s)' % p.doprint(self.function)

    def int_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 3:
                return limit

    def condition_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 2:
                return limit
            if len(limit) == 3: 
                x, a, b = limit
                if a.is_boolean:
                    return
                is_integer = limit[0].is_integer
                return x, Interval(a, b, right_open=is_integer, integer=is_integer)

    def image_set(self):
        function = self.function
        if isinstance(function, FiniteSet) and len(function) == 1:
            condition_limit = self.condition_limit()
            if condition_limit is not None:
                x, condition = condition_limit
                expr, *_ = function
                return expr, x, condition

    @classmethod
    def construct_finite_set(cls, base, start=None, stop=None, x=None):
        if start is None:
            start = S.Zero

        if stop is None:
            stop = base.shape[-1]

        if x is None:
            x = base.generate_free_symbol(start.free_symbols | stop.free_symbols, integer=True)
        return cls(base[x].set, (x, start, stop - 1))

    def finite_set(self):
        function = self.function
        limit = self.int_limit()
        if limit is None:
            return

        x, a, b = limit
        if isinstance(function, FiniteSet):
            if len(function) == 1:
                expr, *_ = function
                if isinstance(expr, Indexed):
                    if len(expr.indices) == 1:
                        base = expr.base
                    else:
                        base = expr.base[expr.indices[:-1]]
                    diff = expr.indices[-1] - x
                    if diff.has(x):
                        return
                    return base[a + diff: b + diff]

    def _latex(self, p):
        finite_set = self.finite_set()
        if finite_set is not None:
            return r"\left\{*%s\right\} " % p._print(finite_set)

        image_set = self.image_set()
        if image_set is not None:
            lamda_expr, lamda_variables, base_set = image_set
            from sympy.sets.conditionset import ConditionSet
            if isinstance(base_set, ConditionSet) and lamda_variables == base_set.variable:
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), p._print(base_set.condition))

#             from sympy.core.containers import Tuple
            if isinstance(lamda_variables, Tuple):
                varsets = [r"%s \in %s" % (p._print(var), p._print(setv)) for var, setv in zip(lamda_variables, base_set)]
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), ', '.join(varsets))

            if base_set.is_Boolean:
                varsets = p._print(base_set)
            else:
                varsets = r"%s \in %s" % (p._print(lamda_variables), p._print(base_set))
            return r"\left\{\left. %s \right| %s \right\}" % (p._print(lamda_expr), varsets)

        if self.is_ConditionSet:
            vars_print = p._print(self.variable)
            if self.base_set.is_UniversalSet:
                return r"\left\{%s \mid %s \right\}" % (vars_print, p._print(self.condition.as_expr()))
    
            return r"\left\{%s \in %s \mid %s \right\}" % (vars_print, p._print(self.base_set), p._print(self.condition))
            
        function = self.function
        limits = self.limits

        if len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex = r"\bigcup_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                tex = r"\bigcup\limits_{%s \in %s} " % tuple([p._print(i) for i in limit])
            else:
                x, a, b = limit
                b -= 1
                tex = r"\bigcup\limits_{%s=%s}^{%s} " % (p._print(x), p._print(a), p._print(b))
        else:

            tex = r"\bigcup\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

        if isinstance(function, Add):
            tex += r"\left(%s\right)" % p._print(function)
        else:
            tex += p._print(function)

        return tex
    
    def _complement(self, universe):
        # DeMorgan's Law
        if self.is_ConditionSet:
            if self.base_set == universe:
                return ~self            

#         else:
#             return Intersection(s.complement(universe) for s in self.args)
    def __invert__(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        from sympy.sets.conditionset import conditionset
        return conditionset(self.variable, condition, self.base_set)

    def invert(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        from sympy.sets.conditionset import conditionset
        return conditionset(self.variable, condition, self.base_set)

    @property
    def _inf(self):
        # We use Min so that sup is meaningful in combination with symbolic
        # interval end points.
        from sympy.functions.elementary.extremum import Min
        return Min(*[set.inf for set in self.args])

    @property
    def _sup(self):
        # We use Max so that sup is meaningful in combination with symbolic
        # end points.
        from sympy.functions.elementary.extremum import Max
        return Max(*[s.sup for s in self.args])

    def _contains(self, other):
        from sympy.sets.contains import Contains
        if other.has(*self.variables):
            return
        from sympy import Exists
        return Exists(Contains(other, self.function), *self.limits)

    @property
    def _measure(self):
        # Measure of a union is the sum of the measures of the sets minus
        # the sum of their pairwise intersections plus the sum of their
        # triple-wise intersections minus ... etc...

        # Sets is a collection of intersections and a set of elementary
        # sets which made up those intersections (called "sos" for set of sets)
        # An example element might of this list might be:
        #    ( {A,B,C}, A.intersect(B).intersect(C) )

        # Start with just elementary sets (  ({A}, A), ({B}, B), ... )
        # Then get and subtract (  ({A,B}, (A int B), ... ) while non-zero
        sets = [(FiniteSet(s), s) for s in self.args]
        measure = 0
        parity = 1
        while sets:
            # Add up the measure of these sets and add or subtract it to total
            measure += parity * sum(inter.measure for sos, inter in sets)

            # For each intersection in sets, compute the intersection with every
            # other set not already part of the intersection.
            sets = ((sos + FiniteSet(newset), newset.intersect(intersection))
                    for sos, intersection in sets for newset in self.args
                    if newset not in sos)

            # Clear out sets with no measure
            sets = [(sos, inter) for sos, inter in sets if inter.measure != 0]

            # Clear out duplicates
            sos_list = []
            sets_list = []
            for set in sets:
                if set[0] in sos_list:
                    continue
                else:
                    sos_list.append(set[0])
                    sets_list.append(set)
            sets = sets_list

            # Flip Parity - next time subtract/add if we added/subtracted here
            parity *= -1
        return measure

    @property
    def _boundary(self):

        def boundary_of_set(i):
            """ The boundary of set i minus interior of all other sets """
            b = self.args[i].boundary
            for j, a in enumerate(self.args):
                if j != i:
                    b = b - a.interior
            return b

        return Union(*map(boundary_of_set, range(len(self.args))))

    def as_relational(self, symbol):
        """Rewrite a Union in terms of equalities and logic operators. """
        if len(self.args) == 2:
            a, b = self.args
            if (a.sup == b.inf and a.inf is S.NegativeInfinity
                    and b.sup is S.Infinity):
                return And(Ne(symbol, a.sup), symbol < b.sup, symbol > a.inf)
        return Or(*[set.as_relational(symbol) for set in self.args])

    @property
    def is_iterable(self):
        return all(arg.is_iterable for arg in self.args)

    def _eval_evalf(self, prec):
        try:
            return Union(*(set._eval_evalf(prec) for set in self.args))
        except (TypeError, ValueError, NotImplementedError):
            import sys
            raise (TypeError("Not all sets are evalf-able"),
                   None,
                   sys.exc_info()[2])

    def __iter__(self):
        import itertools

        # roundrobin recipe taken from itertools documentation:
        # https://docs.python.org/2/library/itertools.html#recipes
        def roundrobin(*iterables):
            "roundrobin('ABC', 'D', 'EF') --> A D E B F C"
            # Recipe credited to George Sakkis
            pending = len(iterables)
            if PY3:
                nexts = itertools.cycle(iter(it).__next__ for it in iterables)
            else:
                nexts = itertools.cycle(iter(it).next for it in iterables)
            while pending:
                try:
                    for next in nexts:
                        yield next()
                except StopIteration:
                    pending -= 1
                    nexts = itertools.cycle(itertools.islice(nexts, pending))

        if all(s.is_iterable for s in self.args):
            return roundrobin(*(iter(arg) for arg in self.args))
        else:
            raise TypeError("Not all constituent sets are iterable")

    @property
    def etype(self):
        return self.function.etype

    def _eval_Abs(self):
        if self.is_ConditionSet:
            ...

    def min(self): 
        return MIN(self.function.min(), *self.limits)        

    def max(self):
        return MAX(self.function.max(), *self.limits)

    def _eval_is_extended_real(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_real
    
    def _eval_is_finite(self):
        if self.function.is_finite is not None:
            return self.function.is_finite

        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain, **x.assumptions0)
                assert _x.type == x.type
                function = function._subs(x, _x)
        return function.is_finite

    def __add__(self, other):
        if other.has(*self.variables) or other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        
        return self.func(self.function + other, *self.limits).simplify()

    @classmethod
    def simplify_Contains(cls, self, e, s):
        if s.is_ConditionSet:
            if e == s.variable:
                cond = s.condition
            else: 
                cond = s.condition._subs(s.variable, e)
                if not s.base_set.is_UniversalSet:
                    cond = And(cond, self.func(e, s.base_set).simplify())
            return cond.copy(equivalent=self)        
    
    @classmethod
    def simplify_NotContains(cls, self, e, s):
        if s.is_ConditionSet:
            if e == s.variable:
                cond = s.condition.invert()
            else: 
                cond = s.condition._subs(s.variable, e).invert()
                if not s.base_set.is_UniversalSet:
                    cond = Or(cond, self.func(e, s.base_set).simplify())
            return cond.copy(equivalent=self)
        
    def _eval_Subset(self, rhs):
        if self.is_ConditionSet:
            sym, condition, base_set = self.variable, self.condition, self.base_set
            if rhs.is_ConditionSet: 
                _sym, _condition, _base_set = rhs.variable, rhs.condition, rhs.base_set
                if sym.type == _sym.type and (base_set == _base_set or base_set in _base_set):
                    if sym != _sym:
                        _condition = _condition._subs(_sym, sym)
                    if condition == _condition:
                        return S.true
                    if condition.is_And:
                        if _condition.is_And and all(eq in condition._argset for eq in _condition.args) or _condition in condition._argset:
                            return S.true
            base_set &= sym.domain
            if base_set in rhs:
                return S.true

    @classmethod
    def identity(cls, self, **_):
        return self.emptySet
    
    @classmethod
    def rewrite_from_Intersection(cls, self):
        for i, union in enumerate(self.args):
            if isinstance(union, cls):
                args = [*self.args]
                del args[i]
                this = self.func(*args)
                function = union.function & this
                return union.func(function, *union.limits).simplify()
        return self

        
class INTERSECTION(Set, ExprWithLimits):
    """
    Represents an intersection of sets as a :class:`Set`.

    """
    operator = Intersection

    def _latex(self, p):
        function = self.function
        limits = self.limits

        if len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex = r"\bigcap_{%s} " % p._print(limit[0])
            else:
                x, a, b = limit
                tex = r"\bigcap\limits_{%s=%s}^{%s} " % tuple([p._print(i) for i in (x, a, b - 1)])
        else:

            tex = r"\bigcap\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

        if isinstance(function, Add):
            tex += r"\left(%s\right)" % p._print(function)
        else:
            tex += p._print(function)

        return tex

    @property
    def is_iterable(self):
        return any(arg.is_iterable for arg in self.args)

    def _contains(self, other):
        from sympy.sets.contains import Contains
        if other.has(*self.variables):
            return
        from sympy import ForAll
        return ForAll(Contains(other, self.function), *self.limits)

    def __iter__(self):
        no_iter = True
        for s in self.args:
            if s.is_iterable:
                no_iter = False
                other_sets = set(self.args) - set((s,))
                other = Intersection(*other_sets, evaluate=False)
                for x in s:
                    c = sympify(other.contains(x))
                    if c is S.true:
                        yield x
                    elif c is S.false:
                        pass
                    else:
                        yield c

        if no_iter:
            raise ValueError("None of the constituent sets are iterable")

    @staticmethod
    def _handle_finite_sets(args):
        from sympy.core.logic import fuzzy_and, fuzzy_bool
        from sympy.core.compatibility import zip_longest

        fs_args, other = sift(args, lambda x: x.is_FiniteSet, binary=True)
        if not fs_args:
            return
        fs_args.sort(key=len)
        s = fs_args[0]
        fs_args = fs_args[1:]

        res = []
        unk = []
        for x in s:
            c = fuzzy_and(fuzzy_bool(o.contains(x)) for o in fs_args + other)
            if c:
                res.append(x)
            elif c is None:
                unk.append(x)
            else:
                pass  # drop arg

        res = FiniteSet(*res, evaluate=False) if res else s.etype.emptySet
        if unk:
            symbolic_s_list = [x for x in s if x.has(Symbol)]
            non_symbolic_s = s - FiniteSet(*symbolic_s_list, evaluate=False)
            while fs_args:
                v = fs_args.pop()
                if all(i == j for i, j in zip_longest(symbolic_s_list, (x for x in v if x.has(Symbol)))):
                    # all the symbolic elements of `v` are the same
                    # as in `s` so remove the non-symbol containing
                    # expressions from `unk`, since they cannot be
                    # contained
                    for x in non_symbolic_s:
                        if x in unk:
                            unk.remove(x)
                else:
                    # if only a subset of elements in `s` are
                    # contained in `v` then remove them from `v`
                    # and add this as a new arg
                    contained = [x for x in symbolic_s_list if sympify(v.contains(x)) is S.true]
                    if contained != symbolic_s_list:
                        other.append(v - FiniteSet(*contained, evaluate=False))
                    else:
                        pass  # for coverage

            other_sets = Intersection(*other)
            if not other_sets:
                return s.etype.emptySet  # b/c we use evaluate=False below
            elif other_sets.is_UniversalSet:
                res += FiniteSet(*unk)
            else:
                res += Intersection(FiniteSet(*unk), other_sets, evaluate=False)
        return res

    def as_relational(self, symbol):
        """Rewrite an Intersection in terms of equalities and logic operators"""
        return And(*[s.as_relational(symbol) for s in self.args])

    """
    precondition: this set should not be empty!
    """

    def min(self): 
        return MAX(self.function.min(), *self.limits)        

    """
    precondition: this set should not be empty!
    """

    def max(self):
        return MIN(self.function.max(), *self.limits)

    # finiteness of intersection set is hard to evaluate
    def _eval_is_finite(self):
        function = self.function                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite

    def simplify(self, deep=False):
        if deep:
            _self = ExprWithLimits.simplify(self, deep=True)
            if _self != self:
                return _self

        return self

    def intersection_sets(self, expr):
        
        if expr.func == self.func:
            if self.function == expr.function:
                limits = self.limits_union(expr)
                return self.func(self.function, *limits)
            else:
                return

        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.function.subs(i, b) == expr:
                    return self.func(self.function, (i, a, b + 1))
                if self.function.subs(i, a - 1) == expr:
                    return self.func(self.function, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.function.subs(i, i_))
                if dic:
                    i_match = dic[i_]
                    if i_match >= a and i_match <= b:
                        return self

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '∩[%s](%s)' % (limits, p.doprint(self.function))
        return '∩(%s)' % p.doprint(self.function)

    def __add__(self, other):
        if other.has(*self.variables) or other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        
        return self.func(self.function + other, *self.limits).simplify()


from sympy.concrete.limits import *
