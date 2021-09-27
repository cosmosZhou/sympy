from sympy.core.basic import Basic
from sympy.core.expr import Expr
from sympy.core.singleton import S, Singleton
from sympy.core.symbol import Dummy, symbols, dtype
from sympy.core.sympify import _sympify, sympify, converter
from sympy.logic.boolalg import And
from sympy.sets.sets import Set, Interval, Union, FiniteSet
from sympy.utilities.misc import filldedent
from sympy.core.logic import fuzzy_or, fuzzy_and
from sympy.sets.sets import ProductSet

Reals = Interval(S.NegativeInfinity, S.Infinity)
ExtendedReals = Interval(S.NegativeInfinity, S.Infinity, left_open=False, right_open=False)


class ImageSet(Set):
    """
    Image of a set under a mathematical function. The transformation
    must be given as a Lambda function which has as many arguments
    as the elements of the set upon which it operates, e.g. 1 argument
    when acting on the set of integers or 2 arguments when acting on
    a complex region.

    This function is not normally called directly, but is called
    from `imageset`.


    Examples
    ========

    >>> from sympy import Symbol, S, pi, Dummy, Lambda
    >>> from sympy.sets.sets import FiniteSet, Interval
    >>> from sympy.sets.fancysets import ImageSet

    >>> x = Symbol('x')
    >>> N = S.Naturals
    >>> squares = ImageSet(Lambda(x, x**2), N) # {x**2 for x in N}
    >>> 4 in squares
    True
    >>> 5 in squares
    False

    >>> FiniteSet(0, 1, 2, 3, 4, 5, 6, 7, 9, 10).intersect(squares)
    {1, 4, 9}

    >>> square_iterable = iter(squares)
    >>> for i in range(4):
    ...     next(square_iterable)
    1
    4
    9
    16

    If you want to get value for `x` = 2, 1/2 etc. (Please check whether the
    `x` value is in `base_set` or not before passing it as args)

    >>> squares.lamda(2)
    4
    >>> squares.lamda(S(1)/2)
    1/4

    >>> n = Dummy('n')
    >>> solutions = ImageSet(Lambda(n, n*pi), S.Integers) # solutions of sin(x) = 0
    >>> dom = Interval(-1, 1)
    >>> dom.intersect(solutions)
    {0}

    See Also
    ========

    sympy.sets.sets.imageset
    """

    def __new__(cls, flambda, *sets):
        from sympy.core.function import Lambda
        if not isinstance(flambda, Lambda):
            raise ValueError('first argument must be a Lambda')
        if flambda is S.IdentityFunction and len(sets) == 1:
            return sets[0]
        if not flambda.expr.free_symbols or not flambda.expr.args:
            return FiniteSet(flambda.expr)

        return Basic.__new__(cls, flambda, *sets)

    lamda = property(lambda self: self.args[0])

    @property
    def base_set(self): 
        return ProductSet(self.args[1:])
    
    @property
    def etype(self):
        return self.lamda.expr.type

    def _latex(self, p):
        from sympy.sets.conditionset import ConditionSet
        if isinstance(self.base_set, ConditionSet) and self.lamda.variables == self.base_set.variable:
            return r"\left\{%s \left| %s \right. \right\}" % (p._print(self.lamda.expr), p._print(self.base_set.condition))

        from sympy.core.containers import Tuple
        if isinstance(self.lamda.variables, Tuple):
            sets = self.args[1:]
            varsets = [r"%s \in %s" % (p._print(var), p._print(setv)) for var, setv in zip(self.lamda.variables, sets)]
    #         return r"\left\{%s\; |\; %s\right\}" % (self._print(s.lamda.expr), ', '.join(varsets))
            return r"\left\{%s \left| %s \right. \right\}" % (p._print(self.lamda.expr), ', '.join(varsets))

        var = self.lamda.variables
        setv = self.base_set
        varsets = r"%s \in %s" % (p._print(var), p._print(setv))
        return r"\left\{%s \left| %s \right. \right\}" % (p._print(self.lamda.expr), varsets)

    def __iter__(self):
        already_seen = set()
        for i in self.base_set:
            val = self.lamda(i)
            if val in already_seen:
                continue
            else:
                already_seen.add(val)
                yield val

    def _is_multivariate(self):
        return len(self.lamda.variables) > 1

    def _contains(self, other):
        from sympy.matrices import Matrix
        from sympy.solvers.solveset import solveset, linsolve
        from sympy.solvers.solvers import solve
        from sympy.utilities.iterables import is_sequence, iterable, cartes
        from sympy.core.function import Lambda
        L = self.lamda
        if is_sequence(other):
            if not is_sequence(L.expr):
                return S.false
            if len(L.expr) != len(other):
                raise ValueError(filldedent('''
    Dimensions of other and output of Lambda are different.'''))
        elif iterable(other):
                raise ValueError(filldedent('''
    `other` should be an ordered object like a Tuple.'''))

        solns = None
        if self._is_multivariate():
            if not is_sequence(L.expr):
                # exprs -> (numer, denom) and check again
                # XXX this is a bad idea -- make the user
                # remap self to desired form
                return other.as_numer_denom() in self.func(
                    Lambda(L.variables, L.expr.as_numer_denom()), self.base_set)
            eqs = [expr - val for val, expr in zip(other, L.expr)]
            variables = L.variables
            free = set(variables)
            if all(i.is_number for i in list(Matrix(eqs).jacobian(variables))):
                solns = list(linsolve([e - val for e, val in
                zip(L.expr, other)], variables))
            else:
                try:
                    syms = [e.free_symbols & free for e in eqs]
                    solns = {}
                    for i, (e, s, v) in enumerate(zip(eqs, syms, other)):
                        if not s:
                            if e != v:
                                return S.false
                            solns[vars[i]] = [v]
                            continue
                        elif len(s) == 1:
                            sy = s.pop()
                            sol = solveset(e, sy)
                            if sol.is_EmptySet:
                                return S.false
                            elif isinstance(sol, FiniteSet):
                                solns[sy] = list(sol)
                            else:
                                raise NotImplementedError
                        else:
                            # if there is more than 1 symbol from
                            # variables in expr than this is a
                            # coupled system
                            raise NotImplementedError
                    solns = cartes(*[solns[s] for s in variables])
                except NotImplementedError:
                    solns = solve([e - val for e, val in
                        zip(L.expr, other)], variables, set=True)
                    if solns:
                        _v, solns = solns
                        # watch for infinite solutions like solving
                        # for x, y and getting (x, 0), (0, y), (0, 0)
                        solns = [i for i in solns if not any(
                            s in i for s in variables)]
        else:
            x = L.variables[0]
            if isinstance(L.expr, Expr):
                # scalar -> scalar mapping
                solnsSet = solveset(L.expr - other, x)
                if solnsSet.is_FiniteSet:
                    solns = list(solnsSet)
                else:
                    msgset = solnsSet
            else:
                # scalar -> vector
                for e, o in zip(L.expr, other):
                    solns = solveset(e - o, x)
                    if solns.is_EmptySet:
                        return S.false
                    for soln in solns:
                        try:
                            if soln in self.base_set:
                                break  # check next pair
                        except TypeError:
                            if self.base_set.contains(soln.evalf()):
                                break
                    else:
                        return S.false  # never broke so there was no True
                return S.true

        if solns is None:
            raise NotImplementedError(filldedent('''
            Determining whether %s contains %s has not
            been implemented.''' % (msgset, other)))
        for soln in solns:
            try:
                if soln in self.base_set:
                    return S.true
            except TypeError:
                return self.base_set.contains(soln.evalf())
        return S.false

    @property
    def is_iterable(self):
        return self.base_set.is_iterable

    def doit(self, **kwargs):
        from sympy.sets.setexpr import SetExpr
        f = self.lamda
        base_set = self.base_set
        return SetExpr(base_set)._eval_func(f).set


class Range(Set):
    """
    Represents a range of integers. Can be called as Range(stop),
    Range(start, stop), or Range(start, stop, step); when step is
    not given it defaults to 1.

    `Range(stop)` is the same as `Range(0, stop, 1)` and the stop value
    (just as for Python ranges) is not included in the Range values.
    """

    def structurally_equal(self, other):
        if not isinstance(other, self.func) or len(self.args) != len(other.args):
            return False
        if self.left_open != other.left_open or self.right_open != other.right_open or self.is_integer != other.is_integer:
            return False
        for x, y in zip(self.args[:3], other.args[:3]):
            if not x.structurally_equal(y):
                return False
        return True

    def simplify(self, deep=False):
        if deep:
            hit = False
            args = [*self.args]
            for i, arg in enumerate(self.args[:3]): 
                _arg = arg.simplify(deep=deep)                

                if _arg != arg:
                    hit = True
                args[i] = _arg
            if hit:
                return self.func(*args).simplify()
        
        if self.is_integer:
            if self.left_open:
                return self.copy(start=self.start + 1, left_open=False)
        return self

    @property
    def is_UniversalSet(self):
        return self.start.is_NegativeInfinity and self.stop.is_Infinity
    
    def intersection_sets(self, b):
        if not (b.is_Interval or b.is_Range):
            if self.is_UniversalSet:
                return b
            return
        # handle (-oo, oo)
        if self.is_UniversalSet:
            if b.is_Interval:
                return b.copy(integer=True)
            return b

        # We can't intersect [0,3] with [x,6] -- we don't know if x>0 or x<0
        if not self._is_comparable(b):
            from sympy import Min, Max
            integer = b.is_integer
            if integer:
                a_start = self.start
                b_start = b.start
    
                start = Max(a_start, b_start)
    
                a_end = self.stop
                b_end = b.stop
    
                stop = Min(a_end, b_end)
                return Range(start, stop)                
            else:
                if b.left_open:
                    if self.start <= b.start:
                        start = b.start
                        left_open = True
                    elif self.start > b.start:
                        start = self.start
                        left_open = False
                    else:
                        return
                else:
                    start = Max(self.start, b.start)
                    left_open = False
                    
                if b.right_open: 
                    stop = Min(self.stop, b.stop)
                    right_open = True                            
                else:
                    if self.stop > b.stop:
                        stop = b.stop
                        right_open = False
                    elif self.stop <= b.stop:
#                                 [a, b), [a, b']
                        stop = self.stop
                        right_open = True
                    else: 
                        return                            
                            
                return Range(start, stop, left_open=left_open, right_open=right_open)

        empty = False

        if self.start <= b.stop and b.start <= self.stop:
            # Get topology right.
            if self.start < b.start:
                start = b.start
                left_open = b.left_open
            elif self.start > b.start:
                start = self.start
                left_open = self.left_open
            else:
                start = self.start
                left_open = self.left_open or b.left_open

            if self.stop < b.stop:
                stop = self.stop
                right_open = self.right_open
            elif self.stop > b.stop:
                stop = b.stop
                right_open = b.right_open
            else:
                stop = self.stop
                right_open = self.right_open or b.right_open

            if stop - start == 0 and (left_open or right_open):
                empty = True
        else:
            empty = True

        if empty:
            return self.etype.emptySet

        return self.func(start, stop, left_open=left_open, right_open=right_open)

    def _union_sets(self, b):
        from sympy import Min, Max
        if self.max() in b: 
            return b.copy(start=Min(self.min(), b.min()), left_open=False, integer=True)
        elif self.min() in b:
            return b.copy(stop=Max(self.max(), b.max()), right_open=False, integer=True)
        elif self in b:
            return b
        elif b in self:
            return self

    def union_sets(self, b):
        from sympy.functions.elementary.miscellaneous import Min, Max
        if b.is_Range:
            if self._is_comparable(b):
                # Non-overlapping intervals
                stop = Min(self.stop, b.stop)
                start = Max(self.start, b.start)
                if (stop < start or
                   (stop == start and (stop not in self and stop not in b))):
                    return 
                else:
                    start = Min(self.start, b.start)
                    stop = Max(self.stop, b.stop)

                    left_open = ((self.start != start or self.left_open) and
                                 (b.start != start or b.left_open))
                    right_open = ((self.stop != stop or self.right_open) and
                                  (b.stop != stop or b.right_open))
                    return self.func(start, stop, left_open=left_open, right_open=right_open)
            else:
                if b.left_open:
                    if self.stop == b.start:
                        return self.func(self.start, b.stop, left_open=self.left_open, right_open=b.right_open) - FiniteSet(b.start)
                else:
                    if self.stop == b.start - 1:
                        if b.start <= b.stop: 
                            return self.func(self.start, b.stop, left_open=self.left_open, right_open=b.right_open) - FiniteSet(self.stop)
                    if self.stop == b.start:
                        if self.stop >= self.start and b.stop >= b.start:
                            return self.copy(stop=b.stop)
                    
                return self._union_sets(b)
            
        if b.is_Interval:
            if self._is_comparable(b): 
                # Non-overlapping intervals
                stop = Min(self.stop, b.stop)
                start = Max(self.start, b.start)
                if (stop < start or
                   (stop == start and (stop not in self and stop not in b))):
                    return 
                else:
                    start = Min(self.start, b.start)
                    stop = Max(self.stop, b.stop)

                    left_open = ((self.start != start or self.left_open) and
                                 (b.start != start or b.left_open))
                    right_open = ((self.stop != stop or self.right_open) and
                                  (b.stop != stop or b.right_open))
                    return self.func(start, stop, left_open=left_open, right_open=right_open)
            else:
                if b.left_open:
                    if self.stop == b.start:
                        return self.func(self.start, b.stop, left_open=self.left_open, right_open=b.right_open) - FiniteSet(b.start)
                else:
                    if self.stop == b.start - 1:
                        if b.start <= b.stop: 
                            return self.func(self.start, b.stop, left_open=self.left_open, right_open=b.right_open) - FiniteSet(self.stop)
                    if self.stop == b.start:
                        return self.copy(stop=b.stop, right_open=b.right_open)
                    
                return self._union_sets(b)
            
        if b.is_UniversalSet:
            return b
        if b.is_Complement:
            U, A = b.args             
            if (U.is_Range or U.is_Interval) and not A & self:
                combined = self | U
                if combined.is_Range or combined.is_Interval:
                    return combined - A 

        # If I have open end points and these endpoints are contained in b
        # But only in case, when endpoints are finite. Because
        # interval does not contain oo or -oo.
        open_left_in_b_and_finite = (self.left_open and
                                         sympify(b.contains(self.start)) is S.true and
                                         self.start.is_finite)
        open_right_in_b_and_finite = (self.right_open and
                                          sympify(b.contains(self.stop)) is S.true and
                                          self.stop.is_finite)
        if open_left_in_b_and_finite or open_right_in_b_and_finite:
            # Fill in my end points and return
            left_open = self.left_open and self.start not in b
            right_open = self.right_open and self.stop not in b            
            new_a = self.copy(left_open=left_open, right_open=right_open)
            return set((new_a, b))
        
        drapeau = False
        stop = self.stop
        right_open = self.right_open
        if right_open:
            if stop in b:
                drapeau = True
                right_open = False
        else: 
            if stop + 1 in b:
                drapeau = True
                stop += 1                                   

        start = self.start
        left_open = self.left_open
        if left_open:
            if start in b:
                drapeau = True
                left_open = False
        else: 
            if start - 1 in b:
                drapeau = True
                start -= 1                                    

        if drapeau:
            new_a = self.func(start + 1 if left_open else start, stop if right_open else stop + 1)
            return set((new_a, b))
        
        if self.is_UniversalSet:
            return self

    def __new__(cls, start=None, stop=None, **kwargs):
         
        assert 'integer' not in kwargs
        if start is None or stop is None:
            if kwargs.get('positive'):
                stop = S.Infinity
                start = S.One
            elif kwargs.get('nonnegative'):
                start = S.Zero
                stop = S.Infinity
            elif kwargs.get('negative'):
                start = S.NegativeInfinity
                stop = S.Zero
                kwargs['right_open'] = True
            elif kwargs.get('nonpositive'):
                start = S.NegativeInfinity
                stop = S.Zero
            else:
                start = S.NegativeInfinity
                stop = S.Infinity
                
            if kwargs.get('odd'):
                return cls(start, stop, left_open=start.is_NegativeInfinity, right_open=True).retain_odd()
            elif kwargs.get('even'):
                return cls(start, stop, left_open=start.is_NegativeInfinity, right_open=True).retain_even()
        else:
            start = _sympify(start)
            stop = _sympify(stop)
            
        if 'left_open' in kwargs:
            left_open = kwargs['left_open']
        else:
            # by default, infinite interval start points are open.
            if start.is_NegativeInfinity:
                left_open = True
            else:
                left_open = False
                
        if 'right_open' in kwargs:
            right_open = kwargs['right_open']
        else:
            # by default, stop points are open.
            right_open = True
                
        
        # evaluate if possible
        if right_open and stop <= start or not right_open and stop < start:
            return S.Zero.emptySet

        if stop == start:
            if left_open or right_open:
                return S.Zero.emptySet
            else:
                if start.is_Infinity or start.is_NegativeInfinity:
                    return start.emptySet                
                return FiniteSet(stop)

        if left_open:
            if start.is_finite:
                if not start.is_integer:
                    start = start.floor().simplify()
                    
                start += 1
                left_open = False
        else:
            if start.is_finite and not start.is_integer: 
                start = start.ceiling().simplify()                
            
        if right_open: 
            if stop.is_finite and not stop.is_integer:
                stop = stop.ceiling().simplify()
            
            if start == stop - 1:
                return FiniteSet(start)                
                
        else:
            if stop.is_finite and not stop.is_integer:
                stop = stop.floor().simplify()

            if left_open:
                if start == stop - 1:
                    return FiniteSet(stop)
            else:
                if start == stop:
                    return FiniteSet(stop)
            
            if stop.is_finite:
                right_open = True
                stop += 1
                
        self = Basic.__new__(cls, start, stop)
        self.left_open = bool(left_open)
        self.right_open = bool(right_open)
        return self        

    def element_symbol(self, excludes=set()):
        return self.generate_var(excludes, **self.etype.dict)

    @property
    def size(self):
        if self.left_open:
            start = self.start + 1
        else:
            start = self.start
        if self.right_open:
            stop = self.stop
        else:
            stop = self.stop + 1
        return stop - start

    @property
    def start(self):
        """
        The left end point of 'self'.

        This property takes the same value as the 'inf' property.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).start
        0

        """
        return self._args[0]

    _inf = left = start

    @classmethod
    def open(cls, a, b):
        """Return an interval including neither boundary."""
        return cls(a, b, True, True)

    @classmethod
    def Lopen(cls, a, b):
        """Return an interval not including the left boundary."""
        return cls(a, b, True, False)

    @classmethod
    def Ropen(cls, a, b):
        """Return an interval not including the right boundary."""
        return cls(a, b, False, True)

    @property
    def stop(self):
        """
        The right end point of 'self'.

        This property takes the same value as the 'sup' property.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).stop
        1

        """
        return self._args[1]

    _sup = right = stop

#     trying to evaluate other \ self
    def _complement(self, other):
        if other == Reals:
            return
        
        from sympy.sets import Integers
        if other == Integers:
            start, stop = S.NegativeInfinity, self.start
            if self.left_open:
                stop += 1
            a = Range(start, stop)
            
            start, stop = self.stop, S.Infinity
            if not self.right_open:
                start += 1    
            b = Range(start, stop)
            
            return a | b

        if other.is_FiniteSet:
            nums = [m for m in other.args if m.is_number]
            if nums == []:
                return

        return Set._complement(self, other)

    @property
    def _boundary(self):
        finite_points = [p for p in (self.start, self.stop) if abs(p) != S.Infinity]
        return FiniteSet(*finite_points)

    def _contains(self, other):
        if not isinstance(other, Expr) or (
                other is S.Infinity or
                other is S.NegativeInfinity or
                other is S.NaN or
                other is S.ComplexInfinity) or other.is_extended_real == False:
            return S.false

        if self.start is S.NegativeInfinity and self.stop is S.Infinity:
            if not other.is_extended_real is None:
                if other.is_integer:
                    return S.true
                return

        if other.is_extended_real == False:
            return S.false
        
        if other.is_extended_real is None:
            return
        
        if self.left_open:
            expr = other > self.start
        else:
            expr = other >= self.start

        if self.right_open:
            expr = And(expr, other < self.stop)
        else:
            expr = And(expr, other <= self.stop)

        return _sympify(expr)

    @property
    def _measure(self):
        return self.stop - self.start

    def doit(self, deep=False, **_):
        if deep:
            return self.copy(start=self.start.doit(), stop=self.stop.doit())
        m = self.min()
        if m.is_Integer:
            M = self.max()
            if M.is_Integer: 
                from sympy import FiniteSet
                return FiniteSet(*range(m, M + 1))
        return self

    def to_mpi(self, prec=53):
        return mpi(mpf(self.start._eval_evalf(prec)), mpf(self.stop._eval_evalf(prec)))

    def _eval_evalf(self, prec):
        return Interval(self.left._eval_evalf(prec), self.right._eval_evalf(prec),
                        left_open=self.left_open, right_open=self.right_open)

    def _is_comparable(self, other):
        is_comparable = self.start.is_comparable
        is_comparable &= self.stop.is_comparable
        is_comparable &= other.start.is_comparable
        is_comparable &= other.stop.is_comparable

        return is_comparable

    @property
    def is_left_unbounded(self):
        """Return ``True`` if the left endpoint is negative infinity. """
        return self.left is S.NegativeInfinity or self.left == Float("-inf")

    @property
    def is_right_unbounded(self):
        """Return ``True`` if the right endpoint is positive infinity. """
        return self.right is S.Infinity or self.right == Float("+inf")

    def as_relational(self, x):
        """Rewrite an interval in terms of inequalities and logic operators."""
        x = sympify(x)
        if self.right_open:
            right = x < self.stop
        else:
            right = x <= self.stop
        if self.left_open:
            left = self.start < x
        else:
            left = self.start <= x
        return And(left, right)

    def _eval_Eq(self, other):
        if not other.is_Range:
            if other.is_FiniteSet:
                if other.is_EmptySet and self.start < self.stop:
                    return S.false
                return
            elif other.is_set:
                return
            return S.false
        from sympy import Equal 
        return And(Equal(self.left, other.left), Equal(self.right, other.right))

    @property
    def free_symbols(self):
        return set().union(*[a.free_symbols for a in self.args[:2]])

    def max(self):
        if self.right_open:
            return self.stop - 1
        return self.stop

    def min(self):
        if self.left_open:
            return self.start + 1
        return self.start

    def __neg__(self):
        assert self.right_open
        assert not self.left_open        
        return self.func(-self.stop + 1, -self.start + 1)
    
    def __add__(self, other):
        other = sympify(other)
        if other.is_Range:
            start = self.min()
            stop = self.max()
            
            start += other.min()
            stop += other.max()
            left_open, right_open = False, False                    
            return self.func(start, stop, left_open=left_open, right_open=right_open)
        
        if other.is_Interval:
            start = self.min()
            stop = self.max()
            
            start += other.start
            stop += other.stop
            left_open, right_open = other.left_open, other.right_open                    
            return Interval(start, stop, left_open=left_open, right_open=right_open)
        
        if other.is_ComplexRegion:
            productset = other.args[0].args
            return other.func((self + productset[0]) @ productset[1])
        
        if other.is_FiniteSet:
            start, stop = self.start, self.stop
            start += other.min()
            stop += other.max()
                        
            if other.is_integer: 
                return self.func(start, stop)
            else: 
                stop -= 1
                return Interval(start, stop)
            
        if not other.is_set:
            start = self.start + other
            stop = self.stop + other
            return self.func(start, stop)

        return Set.__add__(self, other)

    def __mul__(self, k):
        if isinstance(k, Expr):
            a, b = self.args
            start = self.start * k
            stop = self.stop * k
            if k.is_integer:
                if k > 0:
                    return self.func(a * k, b * k - k + 1)
                if k < 0:
                    return self.func(b * k - k, a * k + 1)
                if k == 0:
                    return FiniteSet(0)
                
                return self.func(S.NegativeInfinity, S.Infinity)
            else:
                if k > 0:
                    return Interval(a * k, b * k - k)
                if k < 0:
                    return Interval(b * k - k, a * k)
                if k == 0:
                    return FiniteSet(0)
                
                return Interval(S.NegativeInfinity, S.Infinity)

        return Set.__mul__(self, k)

    def cos(self):
        from sympy.core.numbers import epsilon
        start, stop = self.args
        if self.right_open:
            stop -= epsilon

        from sympy import cos, floor

        n = floor(start / S.Pi)

        m = floor(stop / S.Pi)

        if n.is_even:
            if n == m:
                return self.func(cos(self.stop), cos(start),
                                 left_open=self.right_open,
                                 right_open=self.left_open,
                                 integer=self.is_integer)
        elif n.is_odd:
            if n == m:
                return self.copy(start=cos(start), stop=cos(self.stop))

        return self.func(-1, 1)

    def acos(self):
        from sympy import acos

        start, stop = self.args

        return self.func(acos(stop), acos(start), left_open=self.right_open, right_open=self.left_open, integer=self.is_integer)

    def __truediv__(self, other):
        if self.is_integer:
            if other.is_One:
                return self
            if other.is_NegativeOne: 
                return self.func(self.stop / other, self.start / other,
                                 left_open=self.right_open, right_open=self.left_open, integer=self.is_integer)
        else:
            if other.is_extended_positive: 
                return self.copy(start=self.start / other, stop=self.stop / other)
            if other.is_extended_negative: 
                return self.func(self.stop / other, self.start / other,
                                 left_open=self.right_open, right_open=self.left_open, integer=self.is_integer)

    def _has(self, pattern):
        return self.start._has(pattern) or self.stop._has(pattern)

    def copy(self, **kwargs):
        if 'start' not in kwargs:
            start = self.start
        else:
            start = kwargs['start']
            
        if 'stop' not in kwargs:
            stop = self.stop
        else:
            stop = kwargs['stop']
            
        if 'left_open' not in kwargs:
            left_open = self.left_open
        else:
            left_open = kwargs['left_open']

        if 'right_open' not in kwargs:
            right_open = self.right_open
        else:
            right_open = kwargs['right_open']
            
        if left_open:
            start += 1
        if not right_open:
            stop += 1
        return self.func(start, stop)

    def retain_odd(self):
        i = self.generate_var(integer=True)
        from sympy import Cup
        return Cup[i:self]((2 * i + 1).set)
        
    def retain_even(self):
        i = self.generate_var(integer=True)        
        from sympy import Cup
        return Cup[i:self]((2 * i).set)
        
    def _subs(self, old, new, **hints):
        assert old != new
        if self == old:
            return new
        
        hit = False
        args = list(self.args[:2])
        for i, arg in enumerate(args):
            if not hasattr(arg, '_eval_subs'):
                continue
            arg = arg._subs(old, new, **hints)
            if arg != args[i]:
                hit = True
                args[i] = arg
        if hit:
            start, stop = args
            return self.copy(start=start, stop=stop)
        return self

    @property
    def etype(self):
        return dtype.integer

    def _pretty(self, p): 
        if self.start == self.stop:
            return p._print_seq(self.args[:1], '{', '}')

        else:
            left = '['
            right = ')'

            return p._print_seq(self.args[:2], left, right, delimiter=';')

    def _sympystr(self, _): 
        return '{left_open}{start}{sep} {stop}{right_open}'.format(**{'start': self.start, 'stop': self.stop, 'sep': ';',
                             'left_open': '(' if self.left_open else '[',
                             'right_open': ')' if self.right_open else ']'})

    def handle_finite_sets(self, unk):
        if all(arg.domain in self for arg in unk.args):
            return unk

    def _hashable_content(self):
        """Return a tuple of information about self that can be used to
        compute the hash. If a class defines additional attributes,
        like ``name`` in Symbol, then this method should be updated
        accordingly to return such relevant attributes.

        Defining more than _hashable_content is necessary if __eq__ has
        been defined by a class. See note about this in Basic.__eq__."""

        return self._args + (self.left_open, self.right_open)

    def _eval_is_finite(self):
        return (self.start.is_finite or self.left_open) and (self.stop.is_finite or self.right_open)
    
    def _eval_is_extended_integer(self):
        return True
        
    def _eval_is_super_integer(self):
        return True
    
    def _eval_is_extended_rational(self):
        return True        

    def _eval_is_hyper_rational(self):
        return True
            
    def _eval_is_super_rational(self):
        return True
    
    def _eval_is_extended_real(self):
        return True        

    def _eval_is_hyper_real(self):
        return True
            
    def _eval_is_super_real(self):
        return True
   
    def _eval_is_extended_negative(self):
        if self.min().is_extended_nonnegative:
            return False
        if self.max().is_extended_negative:
            return True

    def _eval_is_extended_positive(self):
        if self.max().is_extended_nonpositive:
            return False
        if self.min().is_extended_positive:
            return True

    def _eval_is_extended_complex(self):
        return True        

    def _eval_is_hyper_complex(self):
        return True

    def _eval_is_algebraic(self):
        return True        

    def _eval_is_zero(self):
        if self.min().is_extended_positive:
            return False
        if self.max().is_extended_negative:
            return False

    def inverse(self):
        return

    def _latex(self, p):
        if self.start == self.stop:
            return r"\left\{%s\right\}" % self._print(self.start)
        elif self.start.is_NegativeInfinity:
            if self.stop.is_Infinity:
                if self.left_open and self.right_open: 
                    return r"\mathbb{Z}"
            elif self.stop.is_NegativeOne:
                if self.left_open and not self.right_open:
                    return r"\mathbb{Z}^-"
                                    
        elif self.stop.is_Infinity:
            if self.start.is_One:
                if not self.left_open and self.right_open:
                    return r"\mathbb{Z}^+"
        
        if self.left_open:
            left = '('
        else:
            left = '['

        if self.right_open:
            right = ')'
        else:
            right = ']'

        return r"\left%s%s; %s\right%s" % (left, p._print(self.start), p._print(self.stop), right)

    @classmethod
    def simplify_Element(cls, self, e, s):
        if s.is_integer and e.is_Add:
            if not s.left_open or s.right_open:
                if S.NegativeOne in e.args:
                    s += S.One
                    e += S.One
                    return self.func(e, s, evaluate=False)
                    
            if s.left_open or not s.right_open:
                if S.One in e.args:
                    s -= S.One
                    e -= S.One
                    return self.func(e, s, evaluate=False)
                
        if e.is_integer == s.is_integer: 
            if s.start is S.NegativeInfinity:
                from sympy import Less, LessEqual
                func = Less if s.right_open else LessEqual
                if e.is_extended_real:
                    return func(e, s.stop)
                return
            if s.stop is S.Infinity:
                from sympy import Greater, GreaterEqual
                func = Greater if s.left_open else GreaterEqual
                if e.is_extended_real:
                    return func(e, s.start).simplify()
                return
            complement = e.domain - s
            if complement.is_FiniteSet:
                return self.invert_type(e, complement).simplify()                
            
    @classmethod
    def simplify_NotElement(cls, self, e, s):
        if s.is_Range and e.is_Add:
            if S.NegativeOne in e.args:
                s += S.One
                e += S.One
                return self.func(e, s, evaluate=False).simplify()
                    
            if S.One in e.args: 
                s += S.NegativeOne
                e -= S.One
                return self.func(e, s, evaluate=False).simplify()

    def _eval_Subset(self, rhs):
        if rhs.is_UniversalSet:
            return S.true
        if rhs.is_Range:
            if self.left_open == rhs.left_open:
                if rhs.start == self.start:
                    if self.right_open == rhs.right_open:
                        if self.stop <= rhs.stop:
                            return S.true
            if self.right_open == rhs.right_open:
                if rhs.stop == self.stop:
                    if self.left_open == rhs.left_open:
                        if self.start >= rhs.start:
                            return S.true               

        if rhs.is_Interval:
            if not rhs.left_open:
                if rhs.start == self.start:
                    if self.right_open == rhs.right_open:
                        if self.stop <= rhs.stop:
                            return S.true
            if rhs.right_open:
                if rhs.stop == self.stop:
                    if self.left_open == rhs.left_open:
                        if self.start >= rhs.start:
                            return S.true
            else:
                if rhs.stop == self.stop - 1:
                    if rhs.left_open:
                        if rhs.start.is_NegativeInfinity:
                            return S.true
                    else:
                        if self.start >= rhs.start:
                            return S.true                
                                               
    @property
    def kwargs(self):
        return {'left_open': self.left_open, 'right_open': self.right_open}
                 
    def _eval_Card(self):
        from sympy import Piecewise
        return Piecewise((self.stop - self.start, self.stop >= self.start), (0, True))


converter[range] = Range


def normalize_theta_set(theta):
    """
    Normalize a Real Set `theta` in the Interval [0, 2*pi). It returns
    a normalized value of theta in the Set. For Interval, a maximum of
    one cycle [0, 2*pi], is returned i.e. for theta equal to [0, 10*pi],
    returned normalized value would be [0, 2*pi). As of now intervals
    with end points as non-multiples of `pi` is not supported.

    Raises
    ======

    NotImplementedError
        The algorithms for Normalizing theta Set are not yet
        implemented.
    ValueError
        The input is not valid, i.e. the input is not a real set.
    RuntimeError
        It is a bug, please report to the github issue tracker.

    Examples
    ========

    >>> from sympy.sets.fancysets import normalize_theta_set
    >>> from sympy import Interval, FiniteSet, pi
    >>> normalize_theta_set(Interval(9*pi/2, 5*pi))
    Interval(pi/2, pi)
    >>> normalize_theta_set(Interval(-3*pi/2, pi/2))
    Interval.Ropen(0, 2*pi)
    >>> normalize_theta_set(Interval(-pi/2, pi/2))
    Union(Interval(0, pi/2), Interval.Ropen(3*pi/2, 2*pi))
    >>> normalize_theta_set(Interval(-4*pi, 3*pi))
    Interval.Ropen(0, 2*pi)
    >>> normalize_theta_set(Interval(-3*pi/2, -pi/2))
    Interval(pi/2, 3*pi/2)
    >>> normalize_theta_set(FiniteSet(0, pi, 3*pi))
    {0, pi}

    """
    from sympy.functions.elementary.trigonometric import _pi_coeff as coeff

    if theta.is_Range or theta.is_Interval:
        interval_len = theta.measure
        # one complete circle
        if interval_len >= 2 * S.Pi:
            if interval_len == 2 * S.Pi and theta.left_open and theta.right_open:
                k = coeff(theta.start)
                return Union(Interval(0, k * S.Pi, left_open=False, right_open=True),
                        Interval(k * S.Pi, 2 * S.Pi, left_open=True, right_open=True))
            return Interval(0, 2 * S.Pi, left_open=False, right_open=True)

        k_start, k_end = coeff(theta.start), coeff(theta.stop)

        if k_start is None or k_end is None:
            raise NotImplementedError("Normalizing theta without pi as coefficient is "
                                    "not yet implemented")
        new_start = k_start * S.Pi
        new_end = k_end * S.Pi

        if new_start > new_end:
            return Union(Interval(S.Zero, new_end, left_open=False, right_open=theta.right_open),
                         Interval(new_start, 2 * S.Pi, left_open=theta.left_open, right_open=True))
        else:
            return Interval(new_start, new_end, left_open=theta.left_open, right_open=theta.right_open)

    elif theta.is_FiniteSet:
        new_theta = []
        for element in theta:
            k = coeff(element)
            if k is None:
                raise NotImplementedError('Normalizing theta without pi as '
                                          'coefficient, is not Implemented.')
            else:
                new_theta.append(k * S.Pi)
        return FiniteSet(*new_theta)

    elif theta.is_Union:
        return Union(*[normalize_theta_set(interval) for interval in theta.args])

    elif theta.is_subset(Reals):
        raise NotImplementedError("Normalizing theta when, it is of type %s is not "
                                  "implemented" % type(theta))
    else:
        raise ValueError(" %s is not a real set" % (theta))


class ComplexRegion(Set):
    """
    Represents the Set of all Complex Numbers. It can represent a
    region of Complex Plane in both the standard forms Polar and
    Rectangular coordinates.

    * Polar Form
      Input is in the form of the ProductSet or Union of ProductSets
      of the intervals of r and theta, & use the flag polar=True.

    Z = {z in C | z = r*[cos(theta) + I*sin(theta)], r in [r], theta in [theta]}

    * Rectangular Form
      Input is in the form of the ProductSet or Union of ProductSets
      of interval of x and y the of the Complex numbers in a Plane.
      Default input type is in rectangular form.

    Z = {z in C | z = x + I*y, x in [Re(z)], y in [Im(z)]}

    Examples
    ========

    >>> from sympy.sets.fancysets import ComplexRegion
    >>> from sympy.sets import Interval
    >>> from sympy import S, I, Union
    >>> a = Interval(2, 3)
    >>> b = Interval(4, 6)
    >>> c = Interval(1, 8)
    >>> c1 = ComplexRegion(a*b)  # Rectangular Form
    >>> c1
    CartesianComplexRegion(ProductSet(Interval(2, 3), Interval(4, 6)))

    * c1 represents the rectangular region in complex plane
      surrounded by the coordinates (2, 4), (3, 4), (3, 6) and
      (2, 6), of the four vertices.

    >>> c2 = ComplexRegion(Union(a*b, b*c))
    >>> c2
    CartesianComplexRegion(Union(ProductSet(Interval(2, 3), Interval(4, 6)), ProductSet(Interval(4, 6), Interval(1, 8))))

    * c2 represents the Union of two rectangular regions in complex
      plane. One of them surrounded by the coordinates of c1 and
      other surrounded by the coordinates (4, 1), (6, 1), (6, 8) and
      (4, 8).

    >>> 2.5 + 4.5*I in c1
    True
    >>> 2.5 + 6.5*I in c1
    False

    >>> r = Interval(0, 1)
    >>> theta = Interval(0, 2*S.Pi)
    >>> c2 = ComplexRegion(r*theta, polar=True)  # Polar Form
    >>> c2  # unit Disk
    PolarComplexRegion(ProductSet(Interval(0, 1), Interval.Ropen(0, 2*pi)))

    * c2 represents the region in complex plane inside the
      Unit Disk centered at the origin.

    >>> 0.5 + 0.5*I in c2
    True
    >>> 1 + 2*I in c2
    False

    >>> unit_disk = ComplexRegion(Interval(0, 1)*Interval(0, 2*S.Pi), polar=True)
    >>> upper_half_unit_disk = ComplexRegion(Interval(0, 1)*Interval(0, S.Pi), polar=True)
    >>> intersection = unit_disk.intersect(upper_half_unit_disk)
    >>> intersection
    PolarComplexRegion(ProductSet(Interval(0, 1), Interval(0, pi)))
    >>> intersection == upper_half_unit_disk
    True

    See Also
    ========

    CartesianComplexRegion
    PolarComplexRegion
    Complexes

    """

    def union_sets(self, b):
        if b.is_EmptySet:
            return
        
        if b.is_subset(Reals):
            # treat a subset of reals as a complex region
            b = ComplexRegion.from_real(b)

        if b.is_ComplexRegion:
            # a in rectangular form
            if (not self.polar) and (not b.polar):
                return ComplexRegion(Union(self.sets, b.sets))
            # a in polar form
            elif self.polar and b.polar:
                return ComplexRegion(Union(self.sets, b.sets), polar=True)
        return None

    def __new__(cls, sets, polar=False):
        if polar is False:
            return CartesianComplexRegion(sets)
        elif polar is True:
            return PolarComplexRegion(sets)
        else:
            raise ValueError("polar should be either True or False")

    @property
    def sets(self):
        """
        Return raw input sets to the self.

        Examples
        ========

        >>> from sympy import Interval, ComplexRegion, Union
        >>> a = Interval(2, 3)
        >>> b = Interval(4, 5)
        >>> c = Interval(1, 7)
        >>> C1 = ComplexRegion(a*b)
        >>> C1.sets
        ProductSet(Interval(2, 3), Interval(4, 5))
        >>> C2 = ComplexRegion(Union(a*b, b*c))
        >>> C2.sets
        Union(ProductSet(Interval(2, 3), Interval(4, 5)), ProductSet(Interval(4, 5), Interval(1, 7)))

        """
        return self.args[0]

    @property
    def psets(self):
        """
        Return a tuple of sets (ProductSets) input of the self.

        Examples
        ========

        >>> from sympy import Interval, ComplexRegion, Union
        >>> a = Interval(2, 3)
        >>> b = Interval(4, 5)
        >>> c = Interval(1, 7)
        >>> C1 = ComplexRegion(a*b)
        >>> C1.psets
        (ProductSet(Interval(2, 3), Interval(4, 5)),)
        >>> C2 = ComplexRegion(Union(a*b, b*c))
        >>> C2.psets
        (ProductSet(Interval(2, 3), Interval(4, 5)), ProductSet(Interval(4, 5), Interval(1, 7)))

        """
        if self.sets.is_ProductSet:
            psets = ()
            psets = psets + (self.sets,)
        else:
            psets = self.sets.args
        return psets

    @property
    def a_interval(self):
        """
        Return the union of intervals of `x` when, self is in
        rectangular form, or the union of intervals of `r` when
        self is in polar form.

        Examples
        ========

        >>> from sympy import Interval, ComplexRegion, Union
        >>> a = Interval(2, 3)
        >>> b = Interval(4, 5)
        >>> c = Interval(1, 7)
        >>> C1 = ComplexRegion(a*b)
        >>> C1.a_interval
        Interval(2, 3)
        >>> C2 = ComplexRegion(Union(a*b, b*c))
        >>> C2.a_interval
        Union(Interval(2, 3), Interval(4, 5))

        """
        a_interval = []
        for element in self.psets:
            a_interval.append(element.args[0])

        a_interval = Union(*a_interval)
        return a_interval

    @property
    def b_interval(self):
        """
        Return the union of intervals of `y` when, self is in
        rectangular form, or the union of intervals of `theta`
        when self is in polar form.

        Examples
        ========

        >>> from sympy import Interval, ComplexRegion, Union
        >>> a = Interval(2, 3)
        >>> b = Interval(4, 5)
        >>> c = Interval(1, 7)
        >>> C1 = ComplexRegion(a*b)
        >>> C1.b_interval
        Interval(4, 5)
        >>> C2 = ComplexRegion(Union(a*b, b*c))
        >>> C2.b_interval
        Interval(1, 7)

        """
        b_interval = []
        for element in self.psets:
            b_interval.append(element.args[1])

        b_interval = Union(*b_interval)
        return b_interval

    @property
    def _measure(self):
        """
        The measure of self.sets.

        Examples
        ========

        >>> from sympy import Interval, ComplexRegion, S
        >>> a, b = Interval(2, 5), Interval(4, 8)
        >>> c = Interval(0, 2*S.Pi)
        >>> c1 = ComplexRegion(a*b)
        >>> c1.measure
        12
        >>> c2 = ComplexRegion(a*c, polar=True)
        >>> c2.measure
        6*pi

        """
        return self.sets._measure

    @classmethod
    def from_real(cls, sets):
        """
        Converts given subset of real numbers to a complex region.

        Examples
        ========

        >>> from sympy import Interval, ComplexRegion
        >>> unit = Interval(0,1)
        >>> ComplexRegion.from_real(unit)
        CartesianComplexRegion(ProductSet(Interval(0, 1), FiniteSet(0)))

        """
        if not sets.is_subset(S.Reals):
            raise ValueError("sets must be a subset of the real line")

        return CartesianComplexRegion(sets * FiniteSet(0))

    def _contains(self, other):
        from sympy.functions import arg, Abs
        from sympy.core.containers import Tuple
        other = sympify(other)
        isTuple = isinstance(other, Tuple)
        if isTuple and len(other) != 2:
            raise ValueError('expecting Tuple of length 2')

        # If the other is not an Expression, and neither a Tuple
        if not isinstance(other, Expr) and not isinstance(other, Tuple):
            return S.false
        # self in rectangular form
        if not self.polar:
            re, im = other if isTuple else other.as_real_imag()
            return fuzzy_or(fuzzy_and([
                pset.args[0]._contains(re),
                pset.args[1]._contains(im)])
                for pset in self.psets)

        # self in polar form
        elif self.polar:
            if other.is_zero:
                # ignore undefined complex argument
                return fuzzy_or(pset.args[0]._contains(S.Zero)
                    for pset in self.psets)
            if isTuple:
                r, theta = other
            else:
                r, theta = Abs(other), arg(other)
            if theta.is_real and theta.is_number:
                # angles in psets are normalized to [0, 2pi)
                theta %= 2 * S.Pi
                return fuzzy_or(fuzzy_and([
                    pset.args[0]._contains(r),
                    pset.args[1]._contains(theta)])
                    for pset in self.psets)


class CartesianComplexRegion(ComplexRegion):
    """
    Set representing a square region of the complex plane.

    Z = {z in C | z = x + I*y, x in [Re(z)], y in [Im(z)]}

    Examples
    ========

    >>> from sympy.sets.fancysets import ComplexRegion
    >>> from sympy.sets.sets import Interval
    >>> from sympy import I
    >>> region = ComplexRegion(Interval(1, 3) * Interval(4, 6))
    >>> 2 + 5*I in region
    True
    >>> 5*I in region
    False

    See also
    ========

    ComplexRegion
    PolarComplexRegion
    Complexes
    """

    polar = False
    variables = symbols('x, y', cls=Dummy)

    def __new__(cls, sets):

        if sets == S.Reals @ S.Reals:
            return S.Complexes

        if all(_a.is_FiniteSet for _a in sets.args) and (len(sets.args) == 2):

            # ** ProductSet of FiniteSets in the Complex Plane. **
            # For Cases like ComplexRegion({2, 4}*{3}), It
            # would return {2 + 3*I, 4 + 3*I}

            # FIXME: This should probably be handled with something like:
            # return ImageSet(Lambda((x, y), x+I*y), sets).rewrite(FiniteSet)
            complex_num = []
            for x in sets.args[0]:
                for y in sets.args[1]:
                    complex_num.append(x + S.ImaginaryUnit * y)
            return FiniteSet(*complex_num)
        else:
            return Set.__new__(cls, sets)

    @property
    def expr(self):
        x, y = self.variables
        return x + S.ImaginaryUnit * y


class PolarComplexRegion(ComplexRegion):
    """
    Set representing a polar region of the complex plane.

    Z = {z in C | z = r*[cos(theta) + I*sin(theta)], r in [r], theta in [theta]}

    Examples
    ========

    >>> from sympy.sets.fancysets import ComplexRegion, Interval
    >>> from sympy import oo, pi, I
    >>> rset = Interval(0, oo)
    >>> thetaset = Interval(0, pi)
    >>> upper_half_plane = ComplexRegion(rset * thetaset, polar=True)
    >>> 1 + I in upper_half_plane
    True
    >>> 1 - I in upper_half_plane
    False

    See also
    ========

    ComplexRegion
    CartesianComplexRegion
    Complexes

    """

    polar = True
    variables = symbols('r, theta', cls=Dummy)

    def __new__(cls, sets):

        new_sets = []
        # sets is Union of ProductSets
        if not sets.is_ProductSet:
            for k in sets.args:
                new_sets.append(k)
        # sets is ProductSets
        else:
            new_sets.append(sets)
        # Normalize input theta
        for k, v in enumerate(new_sets):
            new_sets[k] = ProductSet(v.args[0],
                                     normalize_theta_set(v.args[1]))
        sets = Union(*new_sets)
        return Set.__new__(cls, sets)

    @property
    def expr(self):
        from sympy.functions.elementary.trigonometric import sin, cos
        r, theta = self.variables
        return r * (cos(theta) + S.ImaginaryUnit * sin(theta))


class Complexes(CartesianComplexRegion, metaclass=Singleton):
    """
    The Set of all complex numbers

    Examples
    ========

    >>> from sympy import S, I
    >>> S.Complexes
    Complexes
    >>> 1 + I in S.Complexes
    True

    See also
    ========

    Reals
    ComplexRegion
	"""
    
    is_UniversalSet = True
    
    def __new__(cls):
        return Set.__new__(cls, ProductSet(Reals, Reals))

    def __str__(self):
        return "S.Complexes"

    def _latex(self, p):
        return r"\mathbb{C}"

    def __repr__(self):
        return "S.Complexes"

    def __add__(self, other):
        if not other.shape and other.is_complex:
            return self
        if other.is_set:
            return self
            
        raise Exception("could not add %s, %s" % (self, other))

    def __matmul__(self, other):
        if other.is_set:
            return ProductSet(self, other)
        
        raise Exception("could not multiply %s, %s" % (self, other))

    def __mul__(self, other):
        if other.is_set:
            return ProductSet(self, other)
        if other.is_complex:
            return S.Complexes
        raise Exception("could not multiply %s, %s" % (self, other))

    @property
    def etype(self):
        return dtype.complex

    def _contains(self, other):
        if other.is_complex:
            return True

        
class ExtendedComplexes(CartesianComplexRegion, metaclass=Singleton):
    
    is_UniversalSet = True
    
    def __new__(cls):
        return Set.__new__(cls, ProductSet(ExtendedReals, ExtendedReals))
    
    def __str__(self):
        return "S.ExtendedComplexes"

    def _latex(self, p):
        return r"\mathbb{*C}"

    def __repr__(self):
        return "S.ExtendedComplexes"

    def __add__(self, other):
        return self

    def __matmul__(self, other):
        if other.is_set:
            return ProductSet(self, other)
        
        raise Exception("could not multiply %s, %s" % (self, other))

    def __mul__(self, other):
        if other.is_set:
            return ProductSet(self, other)
        return self

    @property
    def etype(self):
        return dtype.extended_complex

    def _contains(self, other):
        if other.is_extended_complex:
            return True
