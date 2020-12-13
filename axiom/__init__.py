from . import discrete
from . import sets
from . import neuron
from . import statistics
from . import algebre
from . import calculus
from . import geometry

from sympy.core.numbers import oo
from sympy.logic.boolalg import BooleanTrue
from sympy import Contains


def is_zero(eq):
    assert eq.is_Equal
    lhs, rhs = eq.args
    if lhs.is_zero:
        return rhs
    if rhs.is_zero:
        return lhs    


def is_odd(eq):
    power = None
    if eq.is_StrictLessThan:
        assert eq.rhs.is_zero
        power = eq.lhs        
    elif eq.is_Equal:
        if eq.rhs.is_NegativeOne:
            power = eq.lhs
        elif eq.lhs.is_NegativeOne:
            power = eq.rhs
    elif eq.is_Unequal:
        if eq.rhs.is_One:
            power = eq.lhs
        elif eq.lhs.is_One:
            power = eq.rhs

    base, exponent = is_Power(power)
    assert base.is_NegativeOne
    return exponent


def is_even(eq):
    power = None
    if eq.is_StrictGreaterThan:
        assert eq.rhs.is_zero
        power = eq.lhs        
    elif eq.is_Equal:
        if eq.rhs.is_One:
            power = eq.lhs
        elif eq.lhs.is_One:
            power = eq.rhs
    elif eq.is_Unequal:
        if eq.rhs.is_NegativeOne:
            power = eq.lhs
        elif eq.lhs.is_NegativeOne:
            power = eq.rhs

    base, exponent = is_Power(power)
    assert base.is_NegativeOne
    return exponent


def is_nonzero(eq):
    assert eq.is_Unequal
    lhs, rhs = eq.args
    if lhs.is_zero:
        return rhs
    if rhs.is_zero:
        return lhs    


def is_nonnegative(eq):
    assert eq.is_GreaterThan
    lhs, rhs = eq.args
    assert rhs.is_zero
    return lhs    


def is_nonpositive(eq):
    assert eq.is_LessThan
    lhs, rhs = eq.args
    assert rhs.is_zero
    return lhs    


def is_positive(eq):
    assert eq.is_StrictGreaterThan
    lhs, rhs = eq.args
    assert rhs.is_zero
    return lhs    


def is_negative(eq):
    assert eq.is_StrictLessThan
    lhs, rhs = eq.args
    assert rhs.is_zero
    return lhs    


def is_nonemptyset(eq):
    assert eq.is_Unequal
    lhs, rhs = eq.args
    if lhs.is_EmptySet:
        return rhs
    if rhs.is_EmptySet:
        return lhs    

    
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
    return is_nonzero(eq.function), limits    


def forall_is_zero(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return is_zero(eq.function), limits    


def is_Interval(domain, integer=True, end=oo):
    assert domain.is_Interval
    if integer:
        assert domain.is_integer
    if end.is_Infinity:
        assert domain.max().is_Infinity
        return domain.min()
    return domain.min(), domain.max()


def is_real_Interval(domain):
    assert domain.is_Interval
    assert not domain.is_integer
    return domain

    
def limits_is_nonzero_baseset(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond, baseset = limit        
    return x, is_nonzero(cond), baseset


def limits_is_zero_baseset(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond, baseset = limit        
    return x, is_zero(cond), baseset


def limits_is_set(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, S = limit
    assert S.is_set 
    return Contains(x, S)


def limits_is_Interval(limits, integer=True):
    assert len(limits) == 1
    limit = limits[0]
    x, *ab = limit
    if integer:
        assert x.is_integer     
    return [x, *ab]


def limits_is_symbol(limits):
    assert len(limits) == 1
    limit = limits[0]
    assert len(limit) == 1
    x = limit[0]
    assert x.is_symbol 
    return x


def limits_is_Boolean(limits):
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


def limits_is_nonzero(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit        
    return x, is_nonzero(cond)


def limits_is_zero(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit        
    return x, is_zero(cond)


def limits_is_Equal(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_Equal(cond)       
    return x, cond


def limits_is_LessThan(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_LessThan(cond)       
    return x, cond


def limits_is_ForAll(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_ForAll(cond)       
    return x, cond


def limits_is_Contains(limits):
    assert len(limits) == 1
    limit = limits[0]
    x, cond = limit
    is_Contains(cond)       
    return x, cond


def is_Times(self):
    assert self.is_Times
    return self.args


def is_And(self):
    assert self.is_And
    return [*self.args]


def is_Or(self, copy=True):
    assert self.is_Or
    if copy:
        return [*self.args]
    return self.args


def is_Unequal(self):
    assert self.is_Unequal
    return self.args


def is_Equal(self):
    assert self.is_Equal
    return self.args


def is_LessThan(self):
    assert self.is_LessThan
    return self.args


def is_StrictLessThan(self):
    assert self.is_StrictLessThan
    return self.args


def is_StrictGreaterThan(self):
    assert self.is_StrictGreaterThan
    return self.args


def is_GreaterThan(self):
    assert self.is_GreaterThan
    return self.args


def is_Equivalent(self):
    if self.is_Equivalent:
        return self.args
    assert self.is_Equal
    lhs, rhs = self.args
    assert lhs.is_Function and lhs.func.name == 'bool'
    assert rhs.is_Function and rhs.func.name == 'bool'    
    return lhs.arg, rhs.arg


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


def is_Piecewise(self):
    assert self.is_Piecewise
    return self.args


def is_Abs(self):
    assert self.is_Abs
    return self.arg


def is_LAMBDA(self):
    assert self.is_LAMBDA
    return self.args 


def is_MatMul(self):
    assert self.is_MatMul
    return self.args


def is_Power(self):
    assert self.is_Power
    return self.args


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


def is_Union(self):
    assert self.is_Union
    return self.args


def is_Intersection(self):
    assert self.is_Intersection
    return self.args


def is_definition(self):
    assert self.is_Symbol
    definition = self.definition
    assert definition is not None
    return definition


def forall_equality(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_Equal(eq.function)
    return (eq.function, *limits)


def forall_less_than(eq):
    assert eq.is_ForAll
    limits = eq.limits
    is_LessThan(eq.function)
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

