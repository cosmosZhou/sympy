from . import discrete
from . import sets
from . import keras
from . import statistics
from . import algebra
from . import calculus
from . import geometry


def is_zero(eq):
    assert eq.is_Equal
    lhs, rhs = eq.args
    if lhs == 0:
        return rhs
    if rhs == 0:
        return lhs    


def is_odd(eq):
    expr = None
    if eq.is_Less:
        assert eq.rhs.is_zero
        expr = eq.lhs        
    elif eq.is_Equal:
        if eq.rhs.is_NegativeOne:
            expr = eq.lhs
        elif eq.lhs.is_NegativeOne:
            expr = eq.rhs
        elif eq.rhs.is_One:
            expr = eq.lhs   
    elif eq.is_Unequal:
        if eq.rhs == 0:
            expr = eq.lhs
        elif eq.lhs == 0:
            expr = eq.rhs

    if expr.is_Mod:
        n, d = expr.args
        assert d == 2
        return n

    base, exponent = is_Pow(expr)
    assert base.is_NegativeOne
    return exponent


def is_even(eq):
    expr = None
    if eq.is_Greater:
        assert eq.rhs.is_zero
        expr = eq.lhs        
    elif eq.is_Equal:
        if eq.rhs.is_One:
            expr = eq.lhs
        elif eq.lhs.is_One:
            expr = eq.rhs
        elif eq.rhs.is_Zero:
            expr = eq.lhs            
    elif eq.is_Unequal:
        if eq.rhs.is_NegativeOne:
            expr = eq.lhs
        elif eq.lhs.is_NegativeOne:
            expr = eq.rhs

    if expr.is_Mod:
        n, d = expr.args
        assert d == 2
        return n
    
    base, exponent = is_Pow(expr)
    assert base.is_NegativeOne
    return exponent


def is_nonzero(eq):
    assert eq.is_Unequal
    lhs, rhs = eq.args
    if lhs.is_zero:
        return rhs
    if rhs.is_zero:
        return lhs    


def is_infinite_series(fx):
    f, *limits = is_Sum(fx)
    n, a, b = limit_is_Interval(limits, integer=True)
    assert b.is_infinite
    if not a.is_zero:
        f = f._subs(n, n + a)
    return f


def is_nonnegative(eq):
    if eq.is_GreaterEqual:
        lhs, rhs = eq.args
    elif eq.is_LessEqual:
        rhs ,lhs = eq.args
    else:
        return
    assert rhs.is_zero
    return lhs    


def is_nonpositive(eq):
    if eq.is_LessEqual:
        lhs, rhs = eq.args
    elif eq.is_GreaterEqual:
        rhs, lhs = eq.args
    else:
        return
    
    assert rhs.is_zero
    return lhs    


def is_positive(eq):
    if eq.is_Greater:
        lhs, rhs = eq.args
    elif eq.is_Less:
        rhs, lhs = eq.args
    else:
        return
    assert rhs.is_zero
    return lhs
            


def is_negative(eq):
    if eq.is_Less:
        lhs, rhs = eq.args
    elif eq.is_Greater:
        rhs, lhs = eq.args
    else:
        return
    
    assert rhs.is_zero
    return lhs    


def is_nonemptyset(eq):
    assert eq.is_Unequal
    lhs, rhs = eq.args
    if lhs.is_EmptySet:
        return rhs
    if rhs.is_EmptySet:
        return lhs    


def is_ConditionSet(s):
    assert s.is_ConditionSet
    return s.variable, s.condition, s.base_set    


def is_ImageSet(s):
#     assert s.is_UNION
    sym, expr, base_set = s.image_set()    
    return sym, expr, base_set

    
def is_emptyset(eq):
    assert eq.is_Equal
    lhs, rhs = eq.args
    if lhs.is_EmptySet:
        return rhs
    if rhs.is_EmptySet:
        return lhs    


def forall_is_nonzero(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (is_nonzero(eq.function), *limits)    


def forall_is_zero(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (is_zero(eq.function), *limits)    


def forall_is_positive(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (is_positive(eq.function), *limits)


def forall_is_negative(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (is_negative(eq.function), *limits)


def forall_is_nonpositive(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (*is_nonpositive(eq.function), *limits)


def forall_is_nonnegative(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (*is_nonnegative(eq.function), *limits)


def is_Interval(domain, integer=True, end=None):
    assert domain.is_Interval
    if integer:
        assert domain.is_integer
    if end is not None and end.is_Infinity:
        assert domain.max().is_Infinity
        return domain.min()
    if integer:
        return domain.min(), domain.max() + 1
    return domain.args

def is_CartesianSpace(domain):
    assert domain.is_CartesianSpace    
    return domain.args

def is_integer_Interval(domain):
    assert domain.is_Interval
    assert domain.is_integer
    return domain.args


def is_real_Interval(domain):
    assert domain.is_Interval
    assert not domain.is_integer
    return domain

    
def limit_is_nonzero_baseset(limits):
    x, cond, baseset = limit_is_baseset(limits)    
    return x, is_nonzero(cond), baseset


def limit_is_zero_baseset(limits):
    x, cond, baseset = limit_is_baseset(limits)
    return x, is_zero(cond), baseset


def limit_is_baseset(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond, baseset = limit        
    return x, cond, baseset


def limit_is_condition(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit        
    return x, cond


def limit_is_even(limits):
    n, cond, baseset = limit_is_baseset(limits)
    _n = is_even(cond)
    assert n == _n
    a, b = is_Interval(baseset, integer=True, end=None)
    return n, a, b


def limit_is_odd(limits):
    n, cond, baseset = limit_is_baseset(limits)
    _n = is_odd(cond)
    assert n == _n
    a, b = is_Interval(baseset, integer=True, end=None)
    return n, a, b


def limit_is_set(limits):
    assert len(limits) == 1
    limit = limits[0]
    from sympy import Contains
    
    if len(limit) == 3:
        x, a, b = limit
        from sympy import Interval
        S = Interval(a, b, right_open=x.is_integer, integer=x.is_integer)

    elif len(limit) == 2:
        x, S = limit
        assert S.is_set
    else:
        x = limit[0]
        S = x.universalSet

    return x, S
#     return Contains(x, S)


def limit_is_Interval(limits, integer=True, function=None):
    assert len(limits) == 1
    limit = limits[0]
    x, *ab = limit
    if integer:
        assert x.is_integer
    if not ab and function is not None:         
        domain = function.domain_defined(x)
        ab = is_Interval(domain, integer=integer)
        
    return [x, *ab]


def limits_are_Interval(limits, integer=True):
    for limit in limits:
        x, *ab = limit
        if integer:
            assert x.is_integer     
    return limits


def limit_is_symbol(limits):
    assert len(limits) == 1
    limit = limits[0]
    assert len(limit) == 1
    x = limit[0]
    assert x.is_symbol 
    return x


def limit_is_Boolean(limits):
    assert len(limits) == 1
    limit = limits[0]            
    x, cond = limit
    assert cond.is_boolean 
    return x


def limits_are_Boolean(limits):
    variables = []
    for limit in limits:
        if len(limit) == 2:
            x, cond = limit
            assert cond.is_boolean
        else:
            x = limit[0]
        variables.append(x)      
     
    return tuple(variables)


def limits_are_Contains(limits): 
    array = []
    for limit in limits:
        assert len(limit) <= 2
        if len(limit) == 2:
            x, S = limit
            assert S.is_set            
        else:
            x = limit[0]
        array.append(x)
    return tuple(array)


def limit_is_nonzero(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit        
    return x, is_nonzero(cond)


def limit_is_zero(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit        
    return x, is_zero(cond)


def limit_is_Equal(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_Equal(cond)       
    return x, cond


def limit_is_LessThan(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_LessEqual(cond)       
    return x, cond


def limit_is_ForAll(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_ForAll(cond)       
    return x, cond


def limit_is_Contains(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_Contains(cond)       
    return x, cond


def is_Mul(self, copy=False):
    assert self.is_Mul
    if copy:
        return [*self.args]
    return self.args


def is_Add(self, copy=False):
    assert self.is_Add
    if copy:
        return [*self.args]
    return self.args


def is_Substract(self):
    assert self.is_Add
    if len(self.args) > 2:
        positive = []
        negative = []
        for arg in self.args:
            if arg._coeff_isneg():
                negative.append(-arg)
            else:
                positive.append(arg)
        
        return self.func(*positive), self.func(*negative)
    else:
        lhs, rhs = self.args
        if rhs.is_Mul:
            if rhs.args[0].is_NegativeOne:
                rhs = rhs.func(*rhs.args[1:])
                return lhs, rhs
            elif lhs._coeff_isneg():
                return rhs, -lhs
            
        if lhs.is_Mul: 
            if lhs.args[0].is_NegativeOne:
                lhs = lhs.func(*lhs.args[1:])
                return rhs, lhs
    assert False

        
def is_Divide(self):
    if self.is_Mul:
        d_inverse, n = self.args
        if d_inverse.is_Pow:
            d, e = d_inverse.args
            assert e.is_NegativeOne            
        elif d_inverse.is_Rational:
            num, d = d_inverse.as_numer_denom()
            assert num.is_One
        elif n.is_Pow:
            d_inverse, n = n, d_inverse
            d, e = d_inverse.args
            assert e.is_NegativeOne
            
    elif self.is_Add:
        n, d = self.as_numer_denom()
        
    return n, d


def is_Negate(self):
    from sympy import Mul
    arg, *args = is_Mul(self)
    if arg == -1: 
        return Mul(*args)
    assert arg._coeff_isneg
    return Mul(-arg, *args)


def is_And(self, copy=True):
    assert self.is_And
    if copy:
        return [*self.args]    
    return self.args


def is_Or(self, copy=True):
    assert self.is_Or
    if copy:
        return [*self.args]
    return self.args


def is_Unequal(self):
    assert self.is_Unequal
    return self.args


def is_Equal(self, lhs=None, rhs=None):
    assert self.is_Equal
    x, y = self.args
    if rhs is not None:
        if not isinstance(y, rhs):
            x, y = y, x
    elif lhs is not None:
        if not isinstance(x, lhs):
            x, y = y, x        
    return x, y

def is_Relational(self):
    assert self.is_Relational
    return self.args

def is_Mod(self):
    assert self.is_Mod
    return self.args


def is_BinaryCondition(self):
    assert self.is_BinaryCondition
    return self.args


def is_Subset(self):
    assert self.is_Subset
    return self.args

def is_NotSubset(self):
    assert self.is_NotSubset
    return self.args

def is_Supset(self):
    assert self.is_Supset
    return self.args

def is_NotSupset(self):
    assert self.is_NotSupset
    return self.args

def is_Bool(self):
    assert self.is_Bool
    return self.arg


def is_Subs(self):
    assert self.is_Subs
    return self.args


def is_set_comprehension(self): 
    function, *limits = is_UNION(self)
    element_k = is_FiniteSet(function)
    k, a, b = limit_is_Interval(limits)
    assert a.is_zero
    from sympy.concrete.expr_with_limits import LAMBDA
    return LAMBDA[k:a:b](element_k).simplify()


def is_LessEqual(self):
    assert self.is_LessEqual
    return self.args


def is_Less(self):
    assert self.is_Less
    return self.args


def is_Greater(self):
    assert self.is_Greater
    return self.args


def is_GreaterEqual(self):
    assert self.is_GreaterEqual
    return self.args


def is_Equivalent(self):
    assert self.is_Equivalent
    return self.args


def is_Exists(self):
    assert self.is_Exists
    return self.args


def is_ForAll(self):
    assert self.is_ForAll
    return self.args


def is_Contains(self):
    assert self.is_Contains
    return self.args


def is_NotContains(self):
    assert self.is_NotContains
    return self.args


def is_Piecewise(self, copy=False):
    assert self.is_Piecewise
    if copy:
        return [*self.args]
    return self.args


def is_Abs(self):
    assert self.is_Abs
    return self.arg


def is_FractionalPart(self):
    assert self.is_FractionalPart
    return self.arg


def is_Floor(self):
    assert self.is_Floor
    return self.arg


def is_Ceiling(self):
    assert self.is_Ceiling
    return self.arg


def is_Norm(self):
    assert self.is_Norm
    return self.arg


def is_Log(self):
    assert self.is_Log
    return self.arg


def is_Exp(self):
    assert self.is_Exp
    return self.arg


def is_KroneckerDelta(self):
    assert self.is_KroneckerDelta
    return self.args

    
def is_LAMBDA(self):
    assert self.is_LAMBDA
    return self.args 


def is_Sum(self):
    assert self.is_Sum
    return self.args 


def is_Product(self):
    assert self.is_Product
    return self.args 


def is_UNION(self):
    assert self.is_UNION
    return self.args 

def is_INTERSECTION(self):
    assert self.is_INTERSECTION
    return self.args 

def is_MatMul(self):
    assert self.is_MatMul
    return self.args


def is_Maximize(self):
    assert self.is_Maximize
    return self.args

def is_Matrix(self):
    assert self.is_Matrix
    return self.args

def is_BlockMatrix(self):
    assert self.is_BlockMatrix
    return self.args

def is_Minimize(self):
    assert self.is_Minimize
    return self.args

def is_ArgMin(self):
    assert self.is_ArgMin
    return self.args

def is_ArgMax(self):
    assert self.is_ArgMax
    return self.args

def is_Max(self):
    assert self.is_Max
    return self.args


def is_Min(self):
    assert self.is_Min
    return self.args


def is_Pow(self):
    assert self.is_Pow
    return self.args


def is_Square(self):
    assert self.is_Pow
    base, exp = self.args
    assert exp == 2
    return base


def is_Complement(self):
    assert self.is_Complement
    return self.args


def is_FiniteSet(self, size=1):
    assert self.is_FiniteSet
    if size:
        assert len(self) == size
        if size == 1:
            return self.arg
    return self.args


def is_Indexed(self):
    assert self.is_Indexed
    return self.args


def is_Slice(self):
    assert self.is_Slice
    return self.args


def is_Union(self, copy=False):
    assert self.is_Union
    if copy:
        return [*self.args]
    
    return self.args


def is_Intersection(self, copy=False):
    assert self.is_Intersection
    if copy:
        return [*self.args]
    return self.args


def is_definition(self):
    assert self.is_Symbol
    definition = self.definition
    assert definition is not None
    return definition


def forall_eq(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Equal(eq.function)
    return (eq.function, *limits)


def forall_exists(cond):
    fn, *limits_f = is_ForAll(cond)
    fn, *limits_e = is_Exists(fn)    
    return ((fn, *limits_e), *limits_f)


def forall_ne(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Unequal(eq.function)
    return (eq.function, *limits)


def exists_eq(eq):
    assert eq.is_Exists
    limits = eq.limits
    is_Equal(eq.function)
    return (eq.function, *limits)


def forall_subset(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Subset(eq.function)
    return (eq.function, *limits)


def forall_supset(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Supset(eq.function)
    return (eq.function, *limits)


def forall_le(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_LessEqual(eq.function)
    return (eq.function, *limits)


def forall_lt(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Less(eq.function)
    return (eq.function, *limits)


def forall_ou(eq):
    assert eq.is_ForAll
    limits = eq.limits
    eqs = is_Or(eq.function)
    return (eq.function, *limits)


def forall_et(eq):
    assert eq.is_ForAll
    limits = eq.limits
    eqs = is_And(eq.function)
    return (eq.function, *limits)


def exists_et(eq):
    assert eq.is_Exists
    limits = eq.limits
    eqs = is_And(eq.function)
    return (eq.function, *limits)

def exists_ou(eq):
    assert eq.is_Exists
    limits = eq.limits
    eqs = is_Or(eq.function)
    return (eq.function, *limits)

def exists_forall(eq): 
    function, *limits_e = is_Exists(eq)
    function, *limits_f = is_ForAll(function)
    return ((function, *limits_f), *limits_e)


def forall_gt(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Greater(eq.function)
    return (eq.function, *limits)


def forall_ge(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_GreaterEqual(eq.function)
    return (eq.function, *limits)


def is_Sufficient(eq):
    assert eq.is_Sufficient
    return eq.args


def is_Necessary(eq):
    assert eq.is_Necessary
    return eq.args


def forall_contains(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Contains(eq.function)    
    return (eq.function, *limits)


def forall_notcontains(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_NotContains(eq.function)    
    return eq.args


def is_Derivative(self):
    assert self.is_Derivative
    return self.args


def is_Limit(self):
    assert self.is_Limit
    return self.args


def is_limited(given):
    limit, R = is_Contains(given)
    assert R.is_set
    
    expr, *limits = is_Limit(limit)
    if R.is_UniversalSet:
        return (expr, *limits)
    return (expr, *limits, R)

    
def is_continuous(cond):
    eq, *limits = forall_eq(cond)    
    xi, a, b = limit_is_Interval(limits, integer=False)
    limit, fxi = is_Equal(eq)
    fz, (z, xi, dirt) = is_Limit(limit)
    
    assert fz._subs(z, xi) == fxi
    assert dirt == 0
    return fz, (z, a, b)

    
def is_differentiable(cond):
    contains, *limits_f = forall_contains(cond)
    x, ab = limit_is_set(limits_f)
    assert ab.is_Interval
    assert ab.left_open and ab.right_open
    a, b = ab.args
    
    derivative, R = contains.args
    assert R.is_UniversalSet
    
    fx, *limits_d = is_Derivative(derivative)
    assert len(limits_d) == 1
    _x, one = limits_d[0]
    assert _x == x
    assert one == 1
    
    return fx, (x, a, b)


def is_Factorial(self):
    assert self.is_Factorial
    return self.arg