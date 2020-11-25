from . import discrete
from . import sets
from . import neuron
from . import statistics
from . import algebre
from . import calculus
from sympy.core.numbers import oo

def is_zero(eq):
    assert eq.is_Equal
    lhs, rhs = eq.args
    if lhs.is_zero:
        return rhs
    if rhs.is_zero:
        return lhs    

def is_nonzero(eq):
    assert eq.is_Unequal
    lhs, rhs = eq.args
    if lhs.is_zero:
        return rhs
    if rhs.is_zero:
        return lhs    
    
def forall_is_nonzero(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return is_nonzero(eq.function), limits    

def forall_is_zero(eq):
    assert eq.is_ForAll
    limits = eq.limits
    return is_zero(eq.function), limits    

def equality(eq):
    assert eq.is_Equal
    return eq.args

def forall_equality(eq):
    assert eq.is_ForAll
    limits = eq.limits
    eq = equality(eq.function)    
    return eq, limits    

def is_Interval(domain, integer=True, end=oo):
    assert domain.is_Interval
    if integer:
        assert domain.is_integer
    if end.is_Infinity:
        assert domain.max().is_Infinity
        return domain.min()
    return domain.min(), domain.max()
    
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

def is_Times(self):
    assert self.is_Times
    return self.args

def is_And(self):
    assert self.is_And
    return self.args

def is_Unequal(self):
    assert self.is_Unequal
    return self.args
