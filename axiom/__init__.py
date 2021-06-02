from . import sets
from . import keras
from . import stats
from . import algebra
from . import discrete
from . import calculus
from . import geometry

from .algebra import *

def is_infinite_series(fx):
    from sympy import Sum
    f, *limits = fx.of(Sum)
    n, a, b = limit_is_Interval(limits, integer=True)
    assert b.is_infinite
    if not a.is_zero:
        f = f._subs(n, n + a)
    return f


def is_nonnegative(eq):
    if eq.is_GreaterEqual:
        lhs, rhs = eq.args
    elif eq.is_LessEqual:
        rhs , lhs = eq.args
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


def is_ConditionSet(s):
    assert s.is_ConditionSet
    return s.variable, s.condition, s.base_set    


def is_ImageSet(s):
#     assert s.is_Cup
    sym, expr, base_set = s.image_set()    
    return sym, expr, base_set


def all_is_positive(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (is_positive(eq.function), *limits)


def all_is_negative(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (is_negative(eq.function), *limits)


def all_is_nonpositive(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (*is_nonpositive(eq.function), *limits)


def all_is_nonnegative(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return (*is_nonnegative(eq.function), *limits)


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


def limit_is_set(limits):
    assert len(limits) == 1
    limit = limits[0]
    from sympy import Contains
    
    if len(limit) == 3:
        x, a, b = limit
        from sympy import Range
        S = (Range if x.is_integer else Interval)(a, b)

    elif len(limit) == 2:
        x, S = limit
        assert S.is_set
    else:
        x = limit[0]
        S = x.universalSet

    return x, S


def limit_is_Interval(limits, integer=True, function=None):
    assert len(limits) == 1
    limit = limits[0]
    x, *ab = limit
    if integer:
        assert x.is_integer
    if not ab and function is not None: 
        domain = function.domain_defined(x)
        from sympy import Interval
        ab = domain.of(Interval, integer=integer)        
        
    return [x, *ab]


def limits_are_Interval(limits, integer=True):
    for limit in limits:
        x, *ab = limit
        if integer:
            assert x.is_integer     
    return limits


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


def is_Subtract(self):
    assert self.is_Add
    lhs, rhs = self.args
    if rhs.is_Mul:
        if rhs.args[0].is_NegativeOne:
            rhs = rhs.func(*rhs.args[1:])
            return lhs, rhs
        elif lhs._coeff_isneg():
            return rhs, -lhs
            
        
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


def is_set_comprehension(self):
    from sympy import FiniteSet, Cup 
    function, *limits = self.of(Cup)    
    element_k = function.of(FiniteSet)
    k, a, b = limit_is_Interval(limits)
    assert a.is_zero
    from sympy.concrete.expr_with_limits import Lamda
    return Lamda[k:a:b](element_k).simplify()


def is_limited(given):
    from sympy import Contains, Limit
    limit, R = given.of(Contains)
    assert R.is_set
    
    expr, *limits = limit.of(Limit)
    if R.is_UniversalSet:
        return (expr, *limits)
    return (expr, *limits, R)

    
def is_continuous(cond):
    from sympy import Equal, Limit, ForAll
    (limit, fxi), *limits = cond.of(ForAll[Equal])    
    xi, a, b = limit_is_Interval(limits, integer=False)    
    fz, (z, xi, dirt) = limit.of(Limit)
    
    assert fz._subs(z, xi) == fxi
    assert dirt == 0
    return fz, (z, a, b)

    
def is_differentiable(cond):
    from sympy import Derivative, ForAll, Contains, Interval
    (derivative, R), *limits_f = cond.of(ForAll[Contains])
    x, ab = limit_is_set(limits_f)
    a, b = ab.of(Interval)
    
    assert ab.left_open and ab.right_open
    assert R.is_UniversalSet
    
    fx, *limits_d = derivative.of(Derivative)
    assert len(limits_d) == 1
    _x, one = limits_d[0]
    assert _x == x
    assert one == 1
    
    return fx, (x, a, b)
