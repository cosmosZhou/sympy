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
from sympy.sets.sets import Interval, Set, Union, Intersection, FiniteSet
from sympy.sets.fancysets import Range
from sympy.utilities import flatten
from sympy.utilities.iterables import sift, postorder_traversal
from sympy.functions.elementary.miscellaneous import Min, Max
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
                
            elif len(li) == 3:
                oldsymbol, a, b = li 
# added here to remove the domain of this variable!
                if isinstance(oldsymbol, Symbol) and oldsymbol.is_bounded:
                    newsymbol = oldsymbol.unbounded
                    function = function._subs(oldsymbol, newsymbol)
                    limits[i] = Tuple(newsymbol, *li[1:])
                else:
                    if oldsymbol.is_integer and a == b:
                        function = cls.identity(function)
            elif len(li) == 2:
                domain = li[1]
                if domain.is_EmptySet or domain.is_BooleanFalse:
                    function = cls.identity(function)
 
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
        function = function.expr

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
                    if V[1]:
                        x, _, *ab = V
                        if ab:
                            domain = ab[0]
                            if domain.is_Range:
                                start = domain.start
                                stop = domain.stop
                                limits.append(Tuple(x, start, stop))
                            else:
                                limits.append(Tuple(x, domain))
                        else:
                            limits.append(Tuple(x))
                    else:
                        limits.append(Tuple(*V))
                    continue            
                if len(V) == 2:
                    if isinstance(V[1], Range):
                        V = V[0], V[1].start, V[1].stop
                    elif isinstance(V[1], set):
                        V = V[0], FiniteSet(*V[1])
            V = sympify(flatten(V))  # a list of sympified elements
            if isinstance(V[0], (Symbol, Idx)) or getattr(V[0], '_diff_wrt', False):
                newsymbol = V[0]
                if len(V) == 2:
                    if V[1].is_Interval:  # 2 -> 3
                        # Interval
                        V[1:] = [V[1].min(), V[1].max() + 1 if newsymbol.is_integer else V[1].max()]   
                    elif V[1].is_Range:  # 2 -> 3
                    # Interval
                        V[1:] = [V[1].start, V[1].stop if newsymbol.is_integer else V[1].max()]   
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
        return self.expr.is_integer

    def _eval_is_random(self):
        return self.expr.is_random

    def finite_aggregate(self, x, s):
        k, *_ = s.args            
        expr = self.expr._subs(x, k)
        return expr.simplify()

    def limits_intersect(self, expr, clue=None):
        return limits_intersect(self.limits, expr.limits, clue=clue)

    def limits_union(self, expr):
        return limits_union(self.limits, expr.limits)

# precondition, self and other are structurally equal!
    def _dummy_eq(self, other):
        _self = other
        for (x, *ab), (_x, *_ab) in zip(other.limits, self.limits):
            if x != _x:
                if not ab and x.domain != _x.domain:
                    return False
                _self = _self.limits_subs(x, _x)
                if not _self.is_ExprWithLimits:
                    return False
                    
        return _self.limits == self.limits and _self.expr._dummy_eq(self.expr)

    @property
    def limits_dict(self):
        return limits_dict(self.limits)

    @property
    def limits_cond(self):
        return limits_cond(self.limits)

    def limits_update(self, *args):
        return limits_update(self.limits, *args)

    def limits_delete(self, dic):
        return limits_delete(self.limits, dic)

    def limits_common(self, eq, is_or=False):
        return limits_common(self.limits, eq.limits, is_or)

    @property
    def dtype(self):
        return self.expr.dtype

    def __new__(cls, function, *symbols, **assumptions):
        function = sympify(function)
        limits = []
        symbols = [*symbols]
        for i in range(len(symbols) - 1, -1, -1):
            sym = symbols[i]
            if isinstance(sym, tuple):
                sym = Tuple(*sym)
            
            if isinstance(sym, Tuple):
                x, *ab = sym 
                
                if isinstance(x, (Symbol, Indexed, Slice)):
                    if len(sym) == 2:
                        [domain] = ab
                        if domain.is_set:
                            assert x.type in domain.etype or domain.etype in x.type, "domain.etype = %s\n, x.type = %s" % (domain.etype, x.type)
                            if x.is_Symbol and x.is_bounded:
                                domain &= x.domain_bounded
                                _x = x.unbounded
                                sym = _x, domain
                                function = function._subs(x, _x)                            
                            elif domain.is_Range:
                                if domain.is_UniversalSet:
                                    sym = (x,)
                                else:
                                    sym = (x, domain.start, domain.stop)
                            elif domain.is_Interval:
                                if domain.is_UniversalSet:
                                    sym = (x,)
                                elif not domain.left_open and not domain.right_open:
                                    sym = (x, domain.start, domain.stop)
                                    
                            elif domain.is_ConditionSet and domain.variable == x:
                                if domain.base_set.is_UniversalSet:
                                    sym = (x, domain.condition)
                                else:
                                    sym = (x, domain.condition, domain.base_set)
                        elif domain.is_boolean:
                            if domain.is_BinaryCondition:
                                if domain.lhs == x:
                                    if domain.is_GreaterEqual:
                                        sym = (x, domain.rhs, S.Infinity)
                                    elif domain.is_Less:
                                        if x.is_integer:
                                            if x.is_nonnegative:
                                                sym = (x, 0, domain.rhs)
                                                function = function._subs(x, x.unbounded)
                                            else:
                                                sym = (x, -S.Infinity, domain.rhs)
                                    elif domain.is_LessEqual:
                                        if x.is_integer:
                                            ...
                                        else:
                                            if x.is_nonnegative:
                                                sym = (x, 0, domain.rhs)
                                                function = function._subs(x, x.unbounded)
                                            else:
                                                sym = (x, -S.Infinity, domain.rhs)
                                    elif domain.is_Greater:
                                        if x.is_integer:
                                            if domain.rhs.is_integer:
                                                sym = (x, domain.rhs + 1, S.Infinity)
                                        else:
                                            ...    
                                    elif domain.is_Contains:
                                        sym = (x, domain.rhs)
                                elif domain.rhs == x:
                                    if domain.is_LessEqual:  # lhs <= x 
                                        sym = (x, domain.lhs, S.Infinity)
                                    elif domain.is_Greater:  # lhs > x
                                        if x.is_integer:
                                            if x.is_nonnegative:
                                                sym = (x, 0, domain.lhs)
                                                function = function._subs(x, x.unbounded)
                                            else: 
                                                sym = (x, -S.Infinity, domain.lhs)
                                        else:
                                            ...
                                    elif domain.is_GreaterEqual:  # lhs >= x
                                        if x.is_integer:
                                            ...
                                        else:
                                            if x.is_nonnegative:
                                                sym = (x, 0, domain.lhs)
                                                function = function._subs(x, x.unbounded)
                                            else:
                                                sym = (x, -S.Infinity, domain.lhs)
                            elif domain:
                                return function.copy(**assumptions)
                            elif domain.is_BooleanFalse:
                                return cls.identity(function)
                        
                    elif len(sym) == 3:
                        if x.is_Symbol and x.is_bounded and not ab[0].is_boolean:
                            _x = x.unbounded
                            function = function._subs(x, _x)
                            sym = (_x, *ab)
                            
                        a, b = ab
                        if a.is_boolean:
                            if a:
                                if b.is_Range and x.is_integer:
                                    if b.is_UniversalSet:
                                        sym = (x,)
                                    else:
                                        sym = (x, b.start, b.stop)
                                else:
                                    sym = (x, b)
                            elif b.is_UniversalSet:
                                sym = (x, a)
                        elif x.type.is_DtypeInteger and not b.is_set:
                            if a == b - 1:
                                function = function._subs(x, a)                        
                                for j in range(i - 1, -1, -1):
                                    _x, *ab = symbols[j]                
                                    symbols[j] = (_x, *(sympify(e)._subs(x, a) for e in ab))
                                    if _x == x:
                                        break                            
                                    
                                continue
                            elif a == b:
                                return cls.identity(function, **assumptions)
                    
                    limits.append(Tuple(*sym))
                else:
                    if ab:
                        if x.is_BlockMatrix:
                            flat_list = x.args
                        else:
                            flat_list = x._args
                            
                        for arg in flat_list[:0:-1]:
                            limits.append(Tuple(arg,))
                        limits.append(Tuple(flat_list[0], *ab))
                    else:
                        for arg in x._args[::-1]:
                            limits.append(Tuple(arg,))
                    
            else:
                limits.append(Tuple(sym,))
                
        limits.reverse()
    # denest any nested calls
        while cls == type(function):
            limits = list(function.limits) + limits
            function = function.expr

        if not limits and symbols:
            return function.copy(**assumptions)
        
        args = [function] + limits       
        
        if cls.is_Boolean:
            obj = Boolean.__new__(cls, *args, **assumptions)
        else:
            obj = Expr.__new__(cls, *args, **assumptions)

        return obj

    @property
    def expr(self):
        """Return the expression applied across limits.

        Examples
        ========

        >>> from sympy import Integral
        >>> from sympy.abc import x
        >>> Integral(x**2, (x,)).expr
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
        return tuple(l[0] for l in self.limits)

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
        function, limits = self.expr, self.limits
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
            
            for c in ab:
                symbols = c.free_symbols
                if c.is_boolean:
                    symbols -= {var for var in symbols if var._has(x)}
                
                isyms.update(symbols)
        return isyms

    @property
    def is_number(self):
        """Return True if the Sum has no free symbols, else False."""
        return not self.free_symbols

    def _eval_interval(self, x, a, b):
        limits = [(i if i[0] != x else (x, a, b)) for i in self.limits]
        integrand = self.expr
        return self.func(integrand, *limits)

    def _eval_subs(self, old, new, **hints):
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
        func, limits = self.expr, list(self.limits)

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
    
    def _subs_limits(self, x, domain, new, simplify=True):

        def subs(function, x, domain, new):
            if x.is_Slice:
                indexed_set = x.detect_indexed(function)
                if indexed_set:
                    reps = {}
                    _function = function
                    for indexed in indexed_set:
                        indices = indexed.indices
                        for index in indices: 
                            if index.is_symbol:
                                indexDomain = index.domain
                                _indexDomain = self.domain_defined(index)
                                if _indexDomain != indexDomain:
                                    _index = index.copy(domain=_indexDomain)
                                    _function = _function._subs(index, _index)
                                    reps[index] = _index                                
                                       
                    _function = _function._subs(x, new)
                    
                    if reps:
                        for index, _index in reps.items():
                            _function = _function._subs(_index, index)
                else:
                    _function = function._subs(x, new)
            else:
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
                    dom = (Range if x.is_integer else Interval)(*domain)
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

        if self.expr.is_ExprWithLimits and new in self.expr.variables_set:
            if self.expr.is_Any:
                return self
            y = self.expr.generate_var(self.expr.variables_set, **new.type.dict)
            assert new != y
            function = self.expr.limits_subs(new, y)
            if function == self.expr:
                return self
            this = subs(function, x, domain, new)
 
            if this.is_ExprWithLimits:
                if this.expr.is_ExprWithLimits and y in this.expr.variables_set:
                    function = this.expr.limits_subs(y, x)
                else:
                    function = this.expr
     
                this = this.func(function, *this.limits)
                
            if this.is_Boolean:
                this.equivalent = self
            return this
        return subs(self.expr, x, domain, new)

    def limits_subs(self, old, new, simplify=True):
        from sympy.solvers import solve
        if len(self.limits) == 1:
            limit = self.limits[0]
            x, *domain = limit

            if old == x:
                if self.expr._has(new):
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
                            self = self.func(self.expr._subs(old, new), (x, a, b))
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
                                
                        self = self.func(self.expr._subs(old, new), limit)
                        return self.simplify() if simplify else self
                if not new._has(x):
                    return self._subs_limits(x, domain, new, simplify=simplify)

            if len(domain) == 2:
                a, b = domain

            p = old.as_poly(x)

            if p is None or p.degree() != 1:
                if x.is_Slice:
                    x = x.subs(old, new)
                    self = self.func(self.expr.subs(old, new), (x,))
                    return self.simplify() if simplify else self
                return self

            if new.has(x):
                diff = old - new
                if diff._has(x):
                    if old != x: 
                        return self
                    
                    function = self.expr._subs(old, new)
                    if len(domain) == 2:
                        a, b = domain
                        if a.is_boolean:
                            cond, baseset = domain
                            assert baseset.is_set
                            cond = cond._subs(old, new)                            
                            self = self.func(function, (x, cond, baseset))
                        else: 
                            from sympy import Contains
                            cond = Contains(new, (Range if x.is_integer else Interval)(a, b))
                            self = self.func(function, (x, cond))
                    elif len(domain) == 1:
                        cond = domain[0]
                        if cond.is_boolean:
                            cond = cond._subs(old, new)
                            self = self.func(function, (x, cond))
                            
                    return self.simplify() if simplify else self
                    
                else: 
                    if old != x:
                        alpha = p.coeff_monomial(x)
                        diff /= alpha
                        
                    if diff.is_zero:
                        return self
                    
                    function = self.expr._subs(x, x - diff)
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
    
                function = self.expr.subs(x, new)
    
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
            function = self.expr.subs(old, new)

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

                    function = self.expr.subs(x, x - diff)
                    
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
                return self.func(self.expr.subs(old, new), *self.limits)
            
            return self.func(function, *limits)

        return self

    def _if_new_has_variables(self, old, new):
        return {x for x in new.free_symbols & self.variables_set - old.free_symbols if not old._has(x)}
    
    def _subs_if_new_has_variables(self, old, new, intersect=None): 
        this = self
        excludes = self.variables_set | new.free_symbols
        for var in intersect:
            _var = self.generate_var(excludes, integer=True)
            this = this.limits_subs(var, _var)
            excludes.add(_var) 
        _this = this._subs(old, new)
        if _this == this:
            return self
        return _this
        
#     Override this stub if you want to do anything more than
#     attempt a replacement of old with new in the arguments of self.
    def _subs_utility(self, old, new, **hints):
        if old.is_symbol and not self.expr._has(old):
            if not any(limit._has(old) for limit in self.limits):
                return self
            
            intersect = self._if_new_has_variables(old, new)
            if intersect:
                return self._subs_if_new_has_variables(old, new, intersect)
            
            hit = False
            limits = [*self.limits]
            
            for i, limit in enumerate(self.limits):
                _limit = limit._subs_limits(old, new)
                if _limit != limit:
                    limits[i] = _limit
                    hit = True
            if hit:
                self = self.func(self.expr, *limits).simplify()
            return self
            
        intersect = self._if_new_has_variables(old, new)            
        if intersect: 
            return self._subs_if_new_has_variables(old, new, intersect)
        
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
                
                limit = self.limits[i]
                
                if len(limit) <= 1 or not limit[1].is_boolean:
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[i] = _limit
                        hit = True                    
                    
                for j in range(i + 1, len(self.limits)):
                    limit = self.limits[j]
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[j] = _limit
                        hit = True                    
                if hit:
                    self = self.func(self.expr, *limits)
                break
            return self
            
    def _subs_slice_utility(self, old, new, **hints):
        if old.is_symbol and not self.expr._has(old):
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
                self = self.func(self.expr, *limits).simplify()
            return self
            
        intersect = {x for x in new.free_symbols & self.variables_set - old.free_symbols if not old._has(x)}            
        if intersect: 
            this = self
            excludes = self.variables_set | new.free_symbols
            for var in intersect:
                _var = self.generate_var(excludes, integer=True)
                this = this.limits_subs(var, _var)
                excludes.add(_var) 
            _this = this._subs_slice(old, new)
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
                
                limit = self.limits[i]
                
                if len(limit) and limit[1].is_boolean:
                    ...
                else:
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[i] = _limit
                        hit = True                    
                    
                for j in range(i + 1, len(self.limits)):
                    limit = self.limits[j]
                    _limit = limit._subs_limits(old, new)
                    if _limit != limit:
                        limits[j] = _limit
                        hit = True                    
                if hit:
                    self = self.func(self.expr, *limits)
                break
            return self
        
        rule = {}
        for limit in self.limits[::-1]:
            x, *domain = limit
            if x.is_integer and len(domain) == 2:
                a, b = domain
                if a.free_symbols & rule.keys():
                    a = a.subs(rule)
                if b.free_symbols & rule.keys():
                    b = b.subs(rule)
                rule[x] = x.copy(domain=Range(a, b))
        function = self.expr
        if rule:
            function = self.expr.subs(rule)

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

    def _subs_slice(self, old, new, **hints):
        this = self._subs_slice_utility(old, new, **hints)
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
    
    def _has(self, pattern):
        """Helper for .has()"""
#         from sympy.tensor.indexed import Indexed, Slice
        from sympy.core.assumptions import BasicMeta
        from sympy.core.function import UndefinedFunction
        if isinstance(pattern, (BasicMeta, UndefinedFunction)):
            return Expr._has(self, pattern)
        if not isinstance(pattern, (Symbol, Indexed, Slice)):
            return Expr._has(self, pattern)

        function = self.expr
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
                    _x = x.copy(domain=Range(*args))
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
        return self.expr.shape

    def _eval_domain_defined(self, x, allow_empty=True, **_): 
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
                
#             if var.is_integer:
#                 domain &= x.domain_conditioned(a <= b)

        if self.expr._has(x):
            domain &= self.expr.domain_defined(x)
            if x not in self.expr.free_symbols:
                v = self.variable
                if not v.is_Slice:
                    v_domain = self.limits_dict[v]
                    for var in self.expr.free_symbols:
                        if not var._has(v) or not var.is_Indexed:
                            continue
                        pattern = var.subs(v, Wild(v.name, **v.assumptions0))
                        res = x.match(pattern)
                        if res: 
                            t_, *_ = res.values()
                            if isinstance(v_domain, list) or t_ in v_domain:
                                function = self.expr._subs(v, t_)
                                domain &= function.domain_defined(x)
                                break
            
        return domain

    def match_index(self, expr):
        if len(self.limits) != 1:
            return
        
        i, *_ = self.limits[0]
        i_ = Wild(i.name)

        dic = expr.match(self.expr.subs(i, i_))
        if dic:
            return dic[i_]

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
            elif not self.expr.has(var.base[stop - 1]): 
                del dic[var]
                _var = var.base[start: stop - 1]
                if not domain._has(_var):
                    domain = ()
                dic[_var] = domain
                updated = True
            elif not self.expr.has(var.base[start]):
                if not domain._has(var.base[start]):
                    del dic[var]
                    dic[var.base[start + 1: stop]] = domain
                    updated = True
            else:
                from sympy.core.basic import preorder_traversal
                validDomain = S.Zero.emptySet
                for p in preorder_traversal(self.expr):
                    if p.is_Slice and p.base == var.base:
                        validDomain |= Range(*p.indices)
                    elif p.is_Indexed and p.base == var.base:
                        validDomain |= p.indices[0].set
                universe = Range(*var.indices)
                if validDomain != universe and validDomain in universe:
                    if validDomain.is_Range:
                        start, end = validDomain.start, validDomain.stop
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
            return self.func(self.expr, *limits, **kwargs)
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
            if function.is_Range:
                a, b = function.start, function.stop - 1
                return (a + b) * (b - a + 1) / 2
        else:
            function = orientation * function  # orientation not used in ExprWithLimits
            
        return Expr.__new__(cls, function, *limits, **assumptions)

    def _eval_adjoint(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.expr.adjoint(), *self.limits)
        return None

    def _eval_conjugate(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.expr.conjugate(), *self.limits)
        return None

    def _eval_transpose(self):
        if all([x.is_real for x in flatten(self.limits)]):
            return self.func(self.expr.transpose(), *self.limits)
        return None

    def _eval_factor(self, **hints):
        if 1 == len(self.limits):
            summand = self.expr.factor(**hints)
            if summand.is_Mul:
                out = sift(summand.args, lambda w: not set(self.variables) & w.free_symbols)
                return Mul(*out[True]) * self.func(Mul(*out[False]), *self.limits)
        else:
            summand = self.func(self.expr, *self.limits[0:-1]).factor()
            if not summand.has(self.variables[-1]):
                return self.func(1, [self.limits[-1]]).doit() * summand
            elif isinstance(summand, Mul):
                return self.func(summand, self.limits[-1]).factor()
        return self

    def _eval_expand_basic(self, **hints):
        summand = self.expr.expand(**hints)
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
            return Matrix._new(summand.rows, summand.cols, [self.func(i, *self.limits) for i in summand._args])
        elif summand != self.expr:
            if summand._coeff_isneg():
                return -self.func(-summand, *self.limits)
            return self.func(summand, *self.limits)
        
        return self

    def _eval_is_extended_real(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and not domain.is_boolean and not x.shape:
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
                
        return function.is_extended_real
    
    def _eval_is_extended_positive(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and not domain.is_boolean and not x.shape:
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
        return function.is_extended_positive

    def _eval_is_extended_negative(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list) and not domain.is_boolean and not x.shape:
                _x = x.copy(domain=domain)
                if _x != x:
                    function = function._subs(x, _x)
                    
        return function.is_extended_negative


class MINMAXBase(ExprWithLimits):
    
    is_extended_real = True
    
    @property
    def shape(self):
        if self.limits:
            return self.expr.shape
        return self.expr.shape[:-1]
    
    def _eval_is_finite(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite
    
    def simplify(self, deep=False, **kwargs):
        if not self.limits:
            if self.expr.is_Lamda:
                if len(self.expr.limits) == 1 and not self.expr.variable.shape:
                    function = self.expr.expr
                    self = self.func(function, *self.expr.limits).simplify(**kwargs)
            elif self.expr.is_Piecewise:
                self = self.expr.func(*((self.func(e).simplify(), c) for e, c in self.expr.args)).simplify()            
            return self
        (x, *ab), *limits = self.limits
        independent, dependent = self.expr.as_independent(x, as_Add=True)
        if not independent.is_zero: 
            if limits:
                function = self.func(dependent, (x, *ab)) + independent
                return self.func(function, *limits)
            else:
                return self.func(dependent, *self.limits) + independent
        
        independent, dependent = self.expr.as_independent(x, as_Add=False)
        if independent != S.One: 
            if independent.is_extended_negative:
                return self.reversed_type(dependent, *self.limits) * independent
            if independent.is_extended_positive:
                return self.func(dependent, *self.limits) * independent
            if independent._coeff_isneg():
                return -self.func.reversed_type(-self.expr, *self.limits)
            
        if self.expr.is_Log:
            return self.expr.func(self.func(self.expr.arg, *self.limits))
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def bounds(self, x, domain, cls):
        try:
            assert self.expr.is_infinitesimal is None                    
            from sympy import limit
            maxi = domain.max()
            if maxi.is_infinite:
                maxi = limit(self.expr, x, maxi)
#             elif maxi.is_infinitesimal:            
#                 maxi = self.expr._subs(x, maxi, symbol=False)
            else:
                maxi = self.expr._subs(x, maxi, symbol=False)
        
            mini = domain.min()
            if mini.is_infinite:
                mini = limit(self.expr, x, mini)    
#             elif mini.is_infinitesimal:            
#                 mini = self.expr._subs(x, mini, symbol=False)
            else: 
                mini = self.expr._subs(x, mini, symbol=False)
            return cls(maxi, mini)
        except:
            return self
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
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

        if isinstance(self.expr, Add):
            tex += r"\left(%s\right)" % p._print(self.expr)
        else:
            tex += p._print(self.expr)

        return tex

    @property
    def dtype(self):
        if not self.limits:
            if self.expr.is_set:
                return self.expr.etype
        return self.expr.dtype

    def doit(self, **hints):
        if len(self.limits) > 1:
            return self
        
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if not domain:
            domain = x.domain             
            if domain.is_CartesianSpace:
                return self
            
            if domain.is_ComplexRegion:
                return self
        
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
        if self.expr.is_zero:
            return True

    def doit(self, **hints):
        x, *domain = self.limits[0]        
        if len(self.limits) != 1 or x.is_set:
            return MINMAXBase.doit(self, **hints)
        
        if len(domain) == 1:
            [domain] = domain  
        elif len(domain) == 2:            
            domain = (Range if x.is_integer else Interval)(*domain)
        else:
            domain = x.domain
                         
        if domain.is_CartesianSpace or domain.is_ComplexRegion:
            return MINMAXBase.doit(self, **hints)

        if self.expr.is_infinitesimal is not None:
            function, epsilon = self.expr.clear_infinitesimal()
            return self.func(function, *self.limits).doit() + epsilon
        
        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                b = p.nth(0)
                if a.is_positive:
                    return a * domain.min() + b
                elif a.is_negative:
                    return a * domain.max() + b
#             elif p.degree() == 2:
#                 a = p.coeff_monomial(x * x)
#                 if a.is_negative:
#                     return self.bounds(x, domain, Min)                        
#                 elif a.is_positive:
#                     b = p.coeff_monomial(x)
#                     zero_point = -b / (2 * a)
#                     if zero_point in domain:
#                         c = p.nth(0)
#                         return (4 * a * c - b * b) / (4 * a)
#                     return self.bounds(x, domain, Min)
            elif p.degree() == 0:
                return p.nth(0)
            elif p.degree() < 0:
                return self.expr
        elif self.expr.is_MinMaxBase:
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))
            
        return self
    
    def _eval_summation(self, f, x):
        return None
        
    def _eval_is_extended_negative(self):
        if not self.limits and self.expr.is_set:
            if self.expr.infimum().is_extended_negative:
                return True

    def _eval_is_extended_positive(self):
        if not self.limits and self.expr.is_set:
            if self.expr.infimum().is_extended_positive:
                return True
            
    # infimum returns the value which is bound to be below (<=) the minimum!
    def infimum(self):
        if not self.limits and self.expr.is_set:
            return self.expr.infimum()
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
        if self.expr.is_zero:
            return True

    def doit(self, **hints):
        x, *domain = self.limits[0]        
        if len(self.limits) != 1 or x.is_set:
            return MINMAXBase.doit(self, **hints)
            
        if len(domain) == 1:
            [domain] = domain  
        elif len(domain) == 2:            
            domain = (Range if x.is_integer else Interval)(*domain)
        else:
            domain = x.domain
            
        if domain.is_CartesianSpace or domain.is_ComplexRegion:
            return MINMAXBase.doit(self, **hints)

        if self.expr.is_infinitesimal is not None:
            function, epsilon = self.expr.clear_infinitesimal()
            return self.func(function, *self.limits).doit() + epsilon
        
        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1: 
                a = p.coeff_monomial(x)       
                b = p.nth(0)         
                if a.is_extended_positive:
                    return a * domain.max() + b
                elif a.is_extended_negative:
                    return a * domain.min() + b                        
#             elif p.degree() == 2:
#                 a = p.coeff_monomial(x * x)
#                 if a.is_positive:
#                     return self.bounds(x, domain, Max)
#                 elif a.is_negative:
#                     b = p.coeff_monomial(x)
#                     zero_point = -b / (2 * a)
#                     if zero_point in domain:
#                         c = p.nth(0)
#                         return (4 * a * c - b * b) / (4 * a)
#                     return self.bounds(x, domain, Max)
            elif p.degree() == 0:
                return p.nth(0)
            elif p.degree() < 0:
                return self.expr
        elif self.expr.is_MinMaxBase:
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))
                
        return self
    
    def separate(self):
        (x, *_), *_ = self.limits
        if x.is_Slice:
            z, x = x.pop()
            return self.func(self.func(self.expr, (x,)).simplify(), (z,))
        return self

    # supremum returns the value which is bound to be above (>=) the minimum!
    def supremum(self):
        if not self.limits and self.expr.is_set:
            return self.expr.supremum()
        return self

    def _eval_is_extended_positive(self):
        if not self.limits and self.expr.is_set:
            if self.expr.supremum().is_extended_positive:
                return True

    def _eval_is_extended_negative(self):
        if not self.limits and self.expr.is_set:
            if self.expr.supremum().is_extended_negative:
                return True


Maximize.reversed_type = MIN
MIN.reversed_type = Maximize


class ArgMinMaxBase(ExprWithLimits):

    def _eval_is_integer(self):
        return self.variable.is_integer

    def _eval_is_extended_real(self):
        return self.variable.is_extended_real

    def _eval_is_rational(self):
        return self.variable.is_rational
        
    def _eval_is_complex(self):
        return self.variable.is_complex
        
    def _eval_is_zero(self):
        ...

    def _eval_is_extended_positive(self):
        ...

    def _eval_is_extended_negative(self):
        ...

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
            if self.expr.is_Lamda:
                if len(self.expr.limits) == 1 and not self.expr.variable.shape:
                    function = self.expr.expr                    
                    return self.func(function, *self.expr.limits).simplify(**kwargs)
            return self
        * _, (x, *_) = self.limits
        independent, dependent = self.expr.as_independent(x, as_Add=True)
        if not independent.is_zero: 
            return self.func(dependent, *self.limits)
        
        independent, dependent = self.expr.as_independent(x, as_Add=False)
        if independent != S.One:
            if independent.is_extended_positive: 
                return self.func(dependent, *self.limits)
            if independent.is_extended_negative: 
                return self.reversed_type(dependent, *self.limits)            

        if self.expr._coeff_isneg():
            return self.func.reversed_type(-self.expr, *self.limits)
        if self.expr.is_Log:
            return self.func(self.expr.arg, *self.limits)
        
        return ExprWithLimits.simplify(self, deep=deep)
    
    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '%s[%s](%s)' % (self.__class__.__name__, limits, p._print(self.expr))
        return '%s(%s)' % (self.__class__.__name__, p._print(self.expr))
    
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

        if isinstance(self.expr, Add):
            tex += r"\left(%s\right)" % p._print(self.expr)
        else:
            tex += p._print(self.expr)

        return tex


class ArgMin(ArgMinMaxBase):
    r"""Represents unevaluated argmin operator.
    Minimize[f,x]
    minimizes f with respect to x.
    """

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]
        if x.is_set:
            return self

        if len(domain) == 1:
            [domain] = domain  
        elif len(domain) == 2:            
            domain = (Range if x.is_integer else Interval)(*domain)
        else:
            domain = x.domain        
            if domain.is_CartesianSpace:
                return self
        assert self.expr.is_infinitesimal is None
        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_extended_positive:
                    return domain.min()
                elif a.is_extended_negative:
                    return domain.max()
#             elif p.degree() == 2:
#                 a = p.coeff_monomial(x * x)
#                 if a.is_negative:
#                     return self.bounds(x, domain, Min)
#                 elif a.is_positive:
#                     b = p.coeff_monomial(x)
#                     zero_point = -b / (2 * a)
#                     if zero_point in domain:
#                         c = p.nth(0)
#                         delta = 4 * a * c - b * b
#                         from sympy import sqrt
#                         return (-b + sqrt(delta)) / (2 * a)
#                     return self.bounds(x, domain, Min)
            elif p.degree() == 0:
                return self
            elif p.degree() <= 0:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
        elif self.expr.is_MinMaxBase:
            print('warning, unreliable implementation')
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))

        return self
    
            
class ArgMax(ArgMinMaxBase):
    r"""Represents unevaluated argmax operator.
    Maximize[f,x]
    maximizes f with respect to x.
    """

    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def doit(self, **hints):
        if len(self.limits) != 1:
            return self
        x, *domain = self.limits[0]

        if len(domain) == 1:
            [domain] = domain  
        elif len(domain) == 2:            
            domain = (Range if x.is_integer else Interval)(*domain)
        else:
            domain = x.domain
            if domain.is_CartesianSpace:
                return self

        p = self.expr.as_poly(x)

        if p is not None:
            if p.degree() == 1:
                a = p.coeff_monomial(x)
                if a.is_extended_positive:
                    return domain.max()
                elif a.is_extended_negative:
                    return domain.min()
            elif p.degree() == 0:
                return self                
            elif p.degree() <= 0:
                from sympy import ZeroMatrix
                return ZeroMatrix(*self.shape)
        elif self.expr.is_MinMaxBase:
            print('error, unreliable implementation')
            return self.expr.func(*(self.func(arg, *self.limits).doit() for arg in self.expr.args))
                
        return self
    

ArgMax.reversed_type = ArgMin
ArgMin.reversed_type = ArgMax


class Lamda(ExprWithLimits):
    r"""Represents unevaluated Lamda operator.
    >>> n = Symbol.n(integer=True, positive=True)
    >>> A = Symbol.A(shape=(n, n), real=True)
    >>> B = Symbol.B(shape=(n, n), real=True)
    >>> discrete.matmul.to.lamda.apply(A @ B)
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
                        if x.domain == (Range if x.is_integer else Interval)(*domain):
                            symbols[i] = (x,)
                            continue
                    _x = Symbol(x.name, integer=True)
                    symbols[i] = (_x, *domain)

                    function = function.subs(x, _x)
                if len(domain) == 1:
                    domain, *_ = domain
                    assert domain.is_Range
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
        if self.expr.is_zero:
            return True

    def doit(self, deep=False, **hints):
        limit = self.limits[-1]
        x, a, b = limit
        diff = b - a
        if not diff.is_Number:
            return self
        
        limits = self.limits[:-1]
        if limits:
            function = self.func(self.expr, *limits).doit(**hints)
        else:
            function = self.expr
                    
        if deep:
            function = function.doit(deep=deep)
            
        array = []
        for i in range(diff):
            array.append(function._subs(x, sympify(i)))
        return BlockMatrix(*array)

    def as_coeff_mmul(self):
        return 1, self

    def squeeze(self):
        if not self.expr._has(self.variables[-1]):
            limits = self.limits[:-1]
            if limits:
                return self.func(self.expr, *limits).squeeze()
            return self.expr            
        return self
    
    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a Lamda object!
        """
        if rhs.is_Lamda:
            if lhs.limits == rhs.limits:
                from sympy import All
                return All(self.func(lhs.expr, rhs.expr), *lhs.limits).simplify()        

    def simplify(self, deep=False, squeeze=False, **kwargs):
        from sympy import Contains
        limits_dict = self.limits_dict
        if deep:
            function = self.expr
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
                if function != self.expr:
                    return self.func(function, *self.limits).simplify(squeeze=squeeze)
            
        if self.expr.is_Lamda:
            return self.func(self.expr.expr, *self.limits + self.expr.limits).simplify(squeeze=squeeze)
        
        if self.expr.is_Piecewise:
            if len(limits_dict) > 1:
                function = self.func(self.expr, self.limits[0]).simplify(squeeze=squeeze)
                if not function.is_Lamda:
                    return self.func(function, *self.limits[1:]).simplify(squeeze=squeeze)
            else:
                if len(self.expr.args) == 2:
                    e0, c0 = self.expr.args[0]
                    if c0.is_Contains:
                        e, s = c0.args
                        if e in limits_dict.keys():
                            if s.is_Complement:
                                U, A = s.args
                                domain, *_ = limits_dict.values()
                                if domain in U:
                                    e1, _ = self.expr.args[1]
                                    function = self.expr.func((e1, Contains(e, A)), (e0, True)).simplify()
                                    return self.func(function, *self.limits).simplify(squeeze=squeeze)
                            elif s.is_Range:
                                if limits_dict[e] in s:
                                    return self.func(e0, *self.limits).simplify(squeeze=squeeze)
                if self.expr.is_set:
                    return self
                
                constant = None
                args = []
                for e, c in self.expr.args:
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
                this = self.expr.func(*args)
                if second is not None:
                    this += self.func(second, *self.limits).simplify(squeeze=squeeze)
                return this
                    
        from sympy import Transpose
        from sympy.matrices.expressions.matmul import MatMul
        
        if self.expr.is_set:
            independent, dependent = self.simplify_Set(self.expr)
            if independent is not None:
                return independent
            return self
        from sympy.concrete import summations
#         from sympy.matrices.expressions.hadamard import HadamardProduct
        if isinstance(self.expr, summations.Sum) and not self.expr.limits and isinstance(self.expr.expr, Mul):
            (x, *_), *_ = self.limits
            independent, dependent = [], []
            for arg in self.expr.expr.args:
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

        if self.expr.is_Derivative:
            x, n = self.expr.variable_count[0]
            order = 0
            for i, (_i, *_) in zip(x.indices[::-1], self.limits[::-1]):
                if i == _i:
                    order += 1
                    continue
                else:
                    break
            
            x = x.base[x.indices[:-order]]            
            function = self.expr.func(self.expr.expr, (x, n))
            limits = self.limits[:-order]
            if limits:
                return self.func(function, *limits)
            return function

        for i, limit in enumerate(self.limits):
            x, *ab = limit
            if ab:
                a, b = ab
                if a == b:
                    function = self.expr._subs(x, a)                    
                    limits = [*self.limits]
                    del limits[i]
                    if limits:
                        return self.func(function, *limits).simplify()
                    return function
                if not a.is_zero: 
                    function = self.expr._subs(x, x + a)
                    limits = [*self.limits]
                    limits[i] = (x, 0, b - a)
                    return self.func(function, *limits).simplify()
        
        if len(self.limits) > 1:
            this = self.func(self.expr, self.limits[0])
            this_simplified = this.simplify()
            if this == this_simplified:
                return self
            return self.func(this_simplified, *self.limits[1:]).simplify(squeeze=squeeze)
        
        first, second = self.simplify_Plus(self.expr)
        if first is None:
            first, second = self.simplify_Times(self.expr)
            if first is None:
                if self.expr.is_Exp:
                    simplified = self.func(self.expr.args[0], *self.limits).simplify()
                    if not isinstance(simplified, Lamda):
                        return self.expr.func(simplified)
                    
                if squeeze:
                    return self.squeeze()
                
                dependent, independent = self.simplify_MatMul(self.expr)
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
                        if domain == Range(0, base.shape[0]):
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
        
        if expr.is_Mul:
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
        function = self.expr
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
                function = function._subs(x, x + start)
                if stop is None:
                    stop = self.shape[0]
                
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
            indices = sympify(indices)
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
        return self.expr.dtype
    
    @property
    def limits_shape(self):
        shape = []
        for x, *ab in self.limits:
            if not ab:
                domain = self.expr.domain_defined(x)
                shape.append(domain.size)
            else:
                a, b = ab
                shape.append(b - a)
        shape.reverse()
        return tuple(shape)
        
    @property
    def shape(self):
        return self.limits_shape + self.expr.shape

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
                assert domain.is_Range
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
        j = self.generate_var(domain=Range(0, self.cols))
        i = j.generate_var(domain=Range(0, j))
        if self[i, j].is_zero:
            return True

        i = self.generate_var(domain=Range(0, self.rows))
        j = i.generate_var(domain=Range(i + 1, self.cols))
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
        
        j = self.generate_var(domain=Range(0, self.cols))
        i = j.generate_var(domain=Range(j + 1, self.rows))
        if self[i, j].is_zero:
            return True
        
        i = self.generate_var(domain=Range(0, self.rows))
        j = i.generate_var(domain=Range(0, i))
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
        if isinstance(self.expr, (Add, Mul, MatMul)):
            tex += r"\left(%s\right)" % p._print(self.expr)
        else:
            tex += p._print(self.expr)

        return tex

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        return '[%s](%s)' % (limits, p._print(self.expr))

    def _eval_is_finite(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_finite

    def _eval_is_extended_real(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_real

    def _eval_is_complex(self):
        return self.expr.is_complex

    def _eval_is_extended_positive(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_positive

    def _eval_is_extended_negative(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_negative
    
    def _eval_transpose(self):
        if len(self.shape) < 2:
            return self
        if len(self.expr.shape) >= 2:
            return self.func(self.expr.T, *self.limits)
        if len(self.expr.shape) == 1:
            return 
        limits = [*self.limits]
        limits[-1], limits[-2] = limits[-2], limits[-1]
        return self.func(self.expr, *limits).simplify()

    def generate_int_limit(self, index=-1, excludes=None, generator=None, var=None):
        if self.expr.shape:
            len_shape = len(self.expr.shape)
            if index < 0:
                index = len(self.shape) + index
            if index < len_shape:
                return self.expr.generate_int_limit(index, excludes=excludes, generator=generator, var=var)
            index -= len_shape
        limit = self.limits[index]
        if excludes:
            x, *ab = limit
            if x in excludes:
                kwargs = x.type.dict
                if not ab:
                    ab = x.domain.min(), x.domain.max() + 1
                if var is not None and var not in excludes:
                    x = var
                else:
                    x = generator.generate_var(excludes, **kwargs)
                return (x, *ab)
        return limit
        
    def _eval_domain_defined(self, x, **_):
        return ExprWithLimits._eval_domain_defined(self, x, allow_empty=False)        

    def domain_definition(self):
        eqs = []
        for x, *ab in self.limits:
            if ab:
                a, b = ab
                eqs.append(a <= b)
        return And(*eqs)

                
class Cup(Set, ExprWithLimits):
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

    @property
    def is_ConditionSet(self):
        if len(self.limits) != 1:
            return False
        limit = self.limits[0]
        x, *_ = limit
        if not isinstance(x, (Symbol, Indexed, Slice)):
            return False
        if not isinstance(self.expr, FiniteSet) or len(self.expr) != 1:
            return False
        element, *_ = self.expr
        if element != x:
            return False
        if len(limit) <= 1:
            return False
        if len(limit) == 2:
            return True
        
        return limit[2].is_set

    def handle_finite_sets(self, unk):
        if self.is_ConditionSet:
            from sympy.sets import conditionset                    
            return conditionset(self.variable, self.condition, self.base_set & unk)            
        else:
            match_index = self.match_index(unk)
            if match_index is not None:
                if match_index in self.limits_dict[self.variable]:
                    return unk            
            
    def intersection_sets(self, b):
        if self.is_ConditionSet:
            from sympy.sets import conditionset
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
            function = self.func(self.expr, *limits)
        else:
            function = self.expr
        
        return Union(*[function._subs(i, index + a) for index in range(dif)])

    def swap(self):
        if not self.expr.is_Cup:
            return self
        U = self.expr

        return U.func(self.func(U.function, *self.limits).simplify(), *U.limits)

    # this will change the default new operator!
    def __new__(cls, function, *symbols, **assumptions):
        return ExprWithLimits.__new__(cls, function, *symbols, **assumptions)

    def simplify(self, deep=False):
        if deep:
            _self = ExprWithLimits.simplify(self, deep=True)
            if _self != self:
                return _self

        if self.expr.is_Intersection:
            independent = set()
            for arg in self.expr.args:
                if not arg.has(*self.variables):
                    independent.add(arg)
            if independent:
                dependent = self.expr._argset - independent
                function = self.expr.func(*dependent)
                independent = self.expr.func(*independent)
                return self.func(function, *self.limits) & independent

        if len(self.limits) != 1:
            return self
        
        if self.expr.is_EmptySet:
            return self.expr
        
        limit = self.limits[0]

        if len(limit) == 2:
            from sympy.core.relational import Unequal
            x, domain = limit

            if not self.expr._has(x):
                if domain.is_boolean:
                    from sympy import conditionset
                    domain = conditionset(x, domain).simplify()
                return Piecewise((self.expr, Unequal(domain, x.emptySet).simplify()), (self.expr.etype.emptySet, True)).simplify()
            
            if domain.is_FiniteSet and len(domain) == 1:
                return self.finite_aggregate(x, domain)

            if domain.is_EmptySet:
                return self.expr.etype.emptySet

            if domain.is_Union:
                args = []
                success = False
                for dom in domain.args:
                    arg = self.func(self.expr, (x, dom)).simplify()
                    args.append(arg)
                    if not arg.is_Cup or arg.expr != self.expr:
                        success = True
                if success:
                    return Union(*args)

            if domain.is_Range:
                return self.func(self.expr, (x, domain.min(), domain.max() + 1))

            if self.expr.is_Complement:
                A, B = self.expr.args
                if not B.has(*self.variables):
                    return self.func(A, *self.limits) // B

            if domain.is_Piecewise:
                tuples = []
                for e, c in domain.args: 
                    tuples.append((self.func(self.expr, (x, e)).simplify(), c))    
                return domain.func(*tuples)
            if domain.is_boolean:
                if domain.is_Equal:
                    if domain.lhs == x:
                        return self.expr._subs(x, domain.rhs)
                    elif domain.rhs == x:
                        return self.expr._subs(x, domain.lhs)
                elif domain.is_Contains:
                    if domain.lhs == x:
                        return self.func(self.expr, (x, domain.rhs))
                
            if domain.is_set:
                if not domain.is_symbol:
                    image_set = domain.image_set()
                    if image_set:
                        expr, sym, base_set = image_set
                        function = self.expr._subs(x, expr)
                        return self.func(function, (sym, base_set))
                
            if self.is_ConditionSet:
#                 domain = self.limits[0][1]
                if domain.is_set: 
                    return domain
                if domain.is_And:
                    for i, eq in enumerate(domain.args):
                        if eq.is_Contains and eq.lhs == x:
                            eqs = [*domain.args]
                            del eqs[i]                            
                            cond = And(*eqs)
                            return self.func[x:cond:eq.rhs](self.expr)
                            
            return self

        if len(limit) > 2: 
            if limit[2].is_set:
                x, condition, base_set = limit
                # for condition set:
                if self.expr == x.set:
                    domain = x.domain_conditioned(condition)
                    if not domain.is_ConditionSet:
                        return domain & base_set
                    
                if base_set.is_ConditionSet and base_set.variable == x:
                    return self.func[x:condition & base_set.condition:base_set.base_set](self.expr).simplify()
                     
                if condition.domain_defined(x) & self.expr.domain_defined(x) in base_set:
                    return self.func(self.expr, (x, condition))
            else:
                x, a, b = limit
                if a == b - 1:
                    return self.expr._subs(x, a)
                domain = Range(a, b)
                if self.expr.is_Piecewise: 
#                    arr = [arr[-1]] + arr[0:-1]
                    return self.expr.as_multiple_terms(x, domain, self.func).simplify()
                if self.expr.is_FiniteSet:
                    s = self.expr
                    if len(s) == 1 and x == s.arg:
                        return domain
                if not self.expr._has(x):
                    return self.expr
                
                if self.expr.domain_defined(x) in domain:
                    return self.func(self.expr, (x,))

        if len(limit) == 1:
            x = limit[0]
            if self.expr.is_FiniteSet:
                if len(self.expr) == 1:
                    element, *_ = self.expr.args
                    if element == x:
                        return x.domain

            if self.expr.is_Piecewise:
                universe = x.universalSet
                has_x = [c._has(x) for _, c in self.expr.args[:-1]]                                
                if not any(has_x):
                    return self.expr.func(*((self.func(e, (x, universe)).simplify(), c) for e, c in self.expr.args)).simplify()
                
                if all(has_x):
                    return self.expr.as_multiple_terms(x, universe, self.func).simplify()

                if has_x[0]:
                    index = has_x.index(False)
                    
                    independent_of_x = []
                    for arg in self.expr.args[index:]: 
                        independent_of_x.append(arg)
                    independent_of_x = self.expr.func(*independent_of_x)
                    
                    dependent_on_x = []
                    for arg in self.expr.args[:index]: 
                        dependent_on_x.append(arg)
                                            
                    dependent_on_x.append((independent_of_x, True))
                    dependent_on_x = self.expr.func(*dependent_on_x)
                    
                    return self.func(dependent_on_x, *self.limits).simplify()                    
                else: 
                    index = has_x.index(True)
                    dependent_on_x = []
                    for arg in self.expr.args[index:]: 
                        dependent_on_x.append(arg)

                    dependent_on_x = self.expr.func(*dependent_on_x)                    
                    independent_of_x = []
                    for arg in self.expr.args[:index]: 
                        independent_of_x.append(arg)                        
                                            
                    independent_of_x.append((dependent_on_x, True))
                    independent_of_x = self.expr.func(*independent_of_x)
                    
                    return self.func(independent_of_x, *self.limits).simplify()                    
                return self

        return self

    def union_sets(self, expr):
        if expr.is_Complement:
            A, B = expr.args
            if B in self:
                return self | A
        
        if expr.func == self.func:
            if self.expr == expr.expr:
                if self.is_ConditionSet and expr.is_ConditionSet:
                    from sympy.sets import conditionset
                    if self.variable == expr.variable:
                        if self.base_set == expr.base_set: 
                            return conditionset(self.variable, self.condition | expr.condition, self.base_set)
                        if self.condition == expr.condition:
                            return conditionset(self.variable, self.condition, self.base_set | expr.base_set)
                else:
                    limits = self.limits_union(expr)
                    return self.func(self.expr, *limits)

        if self.is_ConditionSet:
            return
        
        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.expr.subs(i, b) == expr:
                    return self.func(self.expr, (i, a, b + 1))
                if self.expr.subs(i, a - 1) == expr:
                    return self.func(self.expr, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.expr.subs(i, i_))
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
                            s = self.expr.subs(i, b)
                            if s == expr or s in expr:
                                deletes.add(b)
                                expr_set |= s
                                
                        if deletes:
                            deletes = FiniteSet(*deletes)
                            B = Complement(B, deletes)
                            expr = Complement(expr, expr_set)
                            if B:
                                A = Complement(A, B)
                            this = self.func(self.expr, (i, A)).simplify()
                            if expr.is_EmptySet:
                                return this
                            return this | expr
                    elif B.is_Complement:
# apply: A \ (B \ C) = (A \ B) | (A & B & C)
                        b, c = B.args
                        domain = Complement(A, b)                        
#                         print(A & b & c)
                        assert Complement(A, Complement(b, c)) == Complement(A, b) | (A & b & c)
                        expr |= self.func(self.expr, (i, A & b & c)).simplify()
                        return expr | self.func(self.expr, (i, domain))

    def _sympystr(self, p):
        if self.is_ConditionSet: 
            return 'ConditionSet(%s)' % ', '.join(p.doprint(arg) for arg in self.limits[0])
        
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '∪[%s](%s)' % (limits, p.doprint(self.expr))
        return '∪(%s)' % p.doprint(self.expr)

    def int_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 3 and not limit[2].is_set:
                return limit

    def condition_limit(self):
        if len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 2:
                return limit
            if len(limit) == 3: 
                x, a, b = limit
                if a.is_boolean:
                    from sympy import conditionset
                    return x, conditionset(x, a, b)
                is_integer = limit[0].is_integer                 
                return x, (Range if is_integer else Interval)(a, b) 
            else:
#                 assert len(limit) == 1
                x = limit[0]
                return x, x.universalSet

    def image_set(self):
        function = self.expr
        if isinstance(function, FiniteSet) and len(function) == 1:
            condition_limit = self.condition_limit()
            if condition_limit is not None:
                x, baseset = condition_limit
                expr, *_ = function
                return x, expr, baseset

    def finite_set(self):
        function = self.expr
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

        if self.is_ConditionSet:
            vars_print = p._print(self.variable)
            if self.base_set.is_UniversalSet:
                return r"\left\{%s \left| %s \right. \right\}" % (vars_print, p._print(self.condition))
    
            return r"\left\{%s \in %s \left| %s \right. \right\}" % (vars_print, p._print(self.base_set), p._print(self.condition))

        image_set = self.image_set()
        if image_set is not None:
            lamda_variables, lamda_expr, base_set = image_set
            if base_set.is_ConditionSet and lamda_variables == base_set.variable:
                if base_set.base_set.is_UniversalSet:
                    return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), p._print(base_set.condition))
                else:
                    return r"\left\{%s \left| %s \wedge %s \in %s \right. \right\}" % (p._print(lamda_expr), p._print(base_set.condition), p._print(base_set.variable), p._print(base_set.base_set))

            if lamda_variables.is_Tuple:
                varsets = [r"%s \in %s" % (p._print(var), p._print(setv)) for var, setv in zip(lamda_variables, base_set)]
                return r"\left\{%s \left| %s \right. \right\}" % (p._print(lamda_expr), ', '.join(varsets))

            if base_set.is_Boolean:
                varsets = p._print(base_set)
            else:
                varsets = r"%s \in %s" % (p._print(lamda_variables), p._print(base_set))
            return r"\left\{ %s \left| %s \right. \right\}" % (p._print(lamda_expr), varsets)
#             return r"\left\{\left. %s \right| %s \right\}" % (p._print(lamda_expr), varsets)

        function = self.expr
        limits = self.limits
        tex = r"\bigcup"
        
        if len(limits) == 1:
            limit = limits[0]
            
            if len(limit) == 1:
                tex += r"_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                x, c = limit
                if c.is_set:
                    tex += r"\limits_{%s \in %s} " % (p._print(x), p._print(c))
                else:
                    tex += r"\limits_{%s \left| %s \right.} " % (p._print(x), p._print(c))
            else:
                x, a, b = limit
                if a.is_Zero and x.is_integer and b.is_symbol:
                    tex += r"\limits_{%s:%s}" % tuple([p._print(s) for s in (x, b)])
                elif b.is_set:
                    tex += r"\limits_{%s \in %s \left| %s \right.} " % (p._print(x), p._print(b), p._print(a))
                else:
                    b -= 1
                    tex += r"\limits_{%s=%s}^{%s} " % (p._print(x), p._print(a), p._print(b))                    
        else:
            if all(len(limit) == 1 for limit in limits):
                tex += r"\limits_{%s} " % str.join(',', [l._format_ineq(p) for l in limits])
            else:
                tex += r"\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

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
            if universe.is_ConditionSet:
                if self.variable == universe.variable and universe.base_set == self.base_set:
                    from sympy.sets import conditionset
                    return conditionset(self.variable, universe.condition & self.condition.invert(), self.base_set)                    

    def __invert__(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        from sympy.sets import conditionset
        return conditionset(self.variable, condition, self.base_set)

    def invert(self):
        assert self.is_ConditionSet
        condition = self.condition.invert()
        from sympy.sets import conditionset
        return conditionset(self.variable, condition, self.base_set)

    @property
    def _inf(self):
        # We use Min so that sup is meaningful in combination with symbolic
        # interval end points.
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*[s.inf for s in self.args])

    @property
    def _sup(self):
        # We use Max so that sup is meaningful in combination with symbolic
        # end points.
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*[s.sup for s in self.args])

    def _contains(self, other):
        from sympy.sets.contains import Contains
        if other.has(*self.variables):
            return
        from sympy import Any
        return Any(Contains(other, self.expr), *self.limits)

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
        return self.expr.etype

    def _eval_Abs(self):
        if self.is_ConditionSet:
            ...

    def min(self): 
        return Minimize(self.expr.min(), *self.limits)        

    def max(self):
        return Maximize(self.expr.max(), *self.limits)

    def _eval_is_extended_real(self):
        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain)
                function = function._subs(x, _x)
        return function.is_extended_real
    
    def _eval_is_finite(self):
        if self.expr.is_finite is not None:
            return self.expr.is_finite

        function = self.expr                
        for x, domain in self.limits_dict.items():
            if not isinstance(domain, list):
                _x = x.copy(domain=domain, **x.assumptions0)
                assert _x.type == x.type
                function = function._subs(x, _x)
        return function.is_finite

    def __add__(self, other):
        if other.has(*self.variables) or other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        
        return self.func(self.expr + other, *self.limits).simplify()

    @classmethod
    def simplify_Contains(cls, self, e, s):
        if s.is_ConditionSet:
            if e == s.variable:
                cond = s.condition
                if not s.base_set.is_UniversalSet:
                    from sympy import Contains
                    cond = And(cond, Contains(e, s.base_set)) 
            else: 
                if s.variable.is_Slice:
                    cond = s.condition._subs_slice(s.variable, e)
                else:
                    cond = s.condition._subs(s.variable, e)
                if not s.base_set.is_UniversalSet:
                    cond = And(cond, self.func(e, s.base_set).simplify())
            return cond        
    
    @classmethod
    def simplify_NotContains(cls, self, e, s):
        if s.is_ConditionSet:
            if e == s.variable:
                cond = s.condition.invert()
            else: 
                cond = s.condition._subs(s.variable, e).invert()
                if not s.base_set.is_UniversalSet:
                    cond = Or(cond, self.func(e, s.base_set).simplify())
            return cond
        
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
        else:
            image_set = self.image_set()
            if image_set is not None:
                _image_set = rhs.image_set()
                if _image_set is not None:
                    x, fx, s = image_set
                    _x, _fx, _s = _image_set
                    if s == _s:
                        if x == _x:
                            if fx == _fx:
                                return S.true
                        else:
                            if fx._subs(x, _x) == _fx:
                                return S.true

    @classmethod
    def identity(cls, self, **_):
        return self.etype.emptySet

    @property
    def is_range_stepped(self):
        expr = self.expr
        if expr.is_FiniteSet:
            limits = self.limits
            if len(limits) == 1 and len(expr) == 1:
                [(i, *ab)] = limits
                if not i.is_integer:
                    return
                
                p = expr.arg.as_poly(i)
                if p and p.degree() == 1:
                    if len(ab) == 1:
                        [domain] = ab
                        if domain.is_boolean:
                            from sympy import conditionset
                            domain = conditionset(i, domain)
                    elif len(ab) == 2:
                        a, b = ab
                        if b.is_set:
                            return
                        domain = Range(a, b)
                    else:
                        domain = expr.domain_defined(i)
                        
                    return p, domain
                         
    def range_contains(self, s):
        if s.is_FiniteSet:
            range_stepped = self.is_range_stepped
            if not range_stepped:
                return
            
            p, domain = range_stepped
            k = p.nth(1)
            h = p.nth(0)
            from sympy import Contains
            
            b = None
            for y in s.args:
                cond = Contains((y - h) / k, domain)
                if cond.is_BooleanTrue:
                    _b = True
                elif cond.is_BooleanFalse:
                    _b = False
                else:
                    return
                if b is None:
                    b = _b
                    
                if b != _b:
                    return
            return b
    
class Cap(Set, ExprWithLimits):
    """
    Represents an intersection of sets as a :class:`Set`.

    """
    operator = Intersection

    def _latex(self, p):
        function = self.expr
        limits = self.limits

        tex = r'\bigcap'
        if len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex += r"_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                tex += r"\limits_{%s \in %s} " % tuple([p._print(i) for i in limit])
            else:
                x, a, b = limit
                tex += r"\limits_{%s=%s}^{%s} " % tuple([p._print(i) for i in (x, a, b - 1)])
        else:
            if all(len(limit) == 1 for limit in limits):
                tex += r"\limits_{%s} " % str.join(',', [l._format_ineq(p) for l in limits])
            else:
                tex += r"\limits_{\substack{%s}} " % str.join('\\\\', [l._format_ineq(p) for l in limits])

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
        from sympy import All
        return All(Contains(other, self.expr), *self.limits)

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
        return MAX(self.expr.min(), *self.limits)        

    """
    precondition: this set should not be empty!
    """

    def max(self):
        return MIN(self.expr.max(), *self.limits)

    # finiteness of intersection set is hard to evaluate
    def _eval_is_finite(self):
        function = self.expr                
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
        if len(self.limits) != 1:
            return self
        
        limit = self.limits[0]
        if len(limit) == 2: 
            from sympy.core.relational import Unequal
            x, domain = limit

            if not self.expr._has(x): 
                if domain.is_boolean:
                    from sympy import conditionset
                    domain = conditionset(x, domain).simplify()
                return Piecewise((self.expr, Unequal(domain, x.emptySet).simplify()), (self.expr.etype.universalSet, True)).simplify()
            
            if domain.is_FiniteSet and len(domain) == 1:
                return self.finite_aggregate(x, domain)

            if domain.is_EmptySet:
                return self.expr.etype.universalSet

            if domain.is_Intersection:
                args = []
                success = False
                for dom in domain.args:
                    arg = self.func(self.expr, (x, dom)).simplify()
                    args.append(arg)
                    if not arg.is_Cap or arg.expr != self.expr:
                        success = True
                if success:
                    return Intersection(*args)

            if domain.is_Range:
                return self.func(self.expr, (x, domain.min(), domain.max() + 1))

            if self.expr.is_Complement:
                A, B = self.expr.args
                if not B.has(*self.variables):
                    return self.func(A, *self.limits) // B

            if domain.is_Piecewise:
                tuples = []
                for e, c in domain.args: 
                    tuples.append((self.func(self.expr, (x, e)).simplify(), c))    
                return domain.func(*tuples)
            if domain.is_boolean:
                if domain.is_Equal:
                    if domain.lhs == x:
                        return self.expr._subs(x, domain.rhs)
                    elif domain.rhs == x:
                        return self.expr._subs(x, domain.lhs)
                elif domain.is_Contains:
                    if domain.lhs == x:
                        return self.func(self.expr, (x, domain.rhs))
                
            if domain.is_set:
                if not domain.is_symbol:
                    image_set = domain.image_set()
                    if image_set:
                        expr, sym, base_set = image_set
                        function = self.expr._subs(x, expr)
                        return self.func(function, (sym, base_set))
                
            if self.is_ConditionSet:
#                 domain = self.limits[0][1]
                if domain.is_set: 
                    return domain
                if domain.is_And:
                    for i, eq in enumerate(domain.args):
                        if eq.is_Contains and eq.lhs == x:
                            eqs = [*domain.args]
                            del eqs[i]                            
                            cond = And(*eqs)
                            return self.func[x:cond:eq.rhs](self.expr)
                            
            return self
        
        if len(limit) == 3:
            x, a, b = limit
            if a == b - 1:
                return self.expr._subs(x, a)
            
            domain = Range(a, b)
            if self.expr.is_FiniteSet:
                s = self.expr
                if len(s) == 1 and x == s.arg:
                    return domain
            if not self.expr._has(x):
                return self.expr
            
            if self.expr.domain_defined(x) in domain:
                return self.func(self.expr, (x,))

        return self

    def intersection_sets(self, expr):
        
        if expr.func == self.func:
            if self.expr == expr.expr:
                limits = self.limits_union(expr)
                return self.func(self.expr, *limits)
            else:
                return

        if len(self.limits) == 1:
            i, *args = self.limits[0]
            if len(args) == 2:
                a, b = args
                if self.expr.subs(i, b) == expr:
                    return self.func(self.expr, (i, a, b + 1))
                if self.expr.subs(i, a - 1) == expr:
                    return self.func(self.expr, (i, a - 1 , b))

                i_ = Wild(i.name)

                dic = expr.match(self.expr.subs(i, i_))
                if dic:
                    i_match = dic[i_]
                    if i_match >= a and i_match <= b:
                        return self

    def _sympystr(self, p):
        limits = ','.join([limit._format_ineq(p) for limit in self.limits])
        if limits:
            return '∩[%s](%s)' % (limits, p.doprint(self.expr))
        return '∩(%s)' % p.doprint(self.expr)

    @property
    def etype(self):
        return self.expr.etype

    def __add__(self, other):
        if other.has(*self.variables) or other.is_set:
            raise Exception("could not add %s, %s" % (self, other))
        
        return self.func(self.expr + other, *self.limits).simplify()

    @classmethod
    def identity(cls, self, **_):
        return self.etype.universalSet


from sympy.concrete.limits import *
