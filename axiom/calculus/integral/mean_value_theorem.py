from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebre, calculus, sets


@apply
def apply(given):
    assert given.is_ForAll
    assert given.function.is_Equality
    assert given.function.lhs.is_Limit
    f, z, xi, direction = given.function.lhs.args
    assert direction.name == '+-'
    assert len(given.limits) == 1
    limit = given.limits[0]
    _xi, a, b = limit
    assert xi == _xi
    _f = f._subs(z, xi)
    assert given.function.rhs == _f

    return Exists(Equality(Integral(f, (z, a, b)), (b - a) * _f), limit)


@prove
def prove(Eq): 

    a = Symbol.a(real=True)
    b = Symbol.b(real=True, domain=Interval(a, oo, left_open=True))

    assert b > a 
    assert b - a > 0
    
    f = Function.f(shape=(), real=True)
    given = calculus.integral.intermediate_value_theorem.continuity(f, a, b)
    
    z = given.lhs.args[1]

    Eq << apply(given)
    
    m = Symbol.m(definition=MIN(f(z), (z, a, b)))
    M = Symbol.M(definition=MAX(f(z), (z, a, b)))
    
    Eq.min, Eq.max = m.equality_defined(), M.equality_defined()
    
    Eq << axiom.calculus.integral.intermediate_value_theorem.apply(given)
    
    Eq.intermediate_value = Eq[-1].this.limits[0][2].subs(Eq.max.reversed).this.limits[0][1].subs(Eq.min.reversed)
    
    Eq << algebre.imply.forall_less_than.min.apply(m.definition)
    
    Eq << algebre.forall_less_than.imply.less_than.integrate.apply(Eq[-1]) 
    
    Eq << Eq[-1].subs(Eq.min.reversed) / (b - a)
    
    Eq << algebre.imply.forall_greater_than.max.apply(M.definition)
    
    Eq << algebre.forall_greater_than.imply.greater_than.integrate.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.max.reversed) / (b - a)
    
    Eq <<= sets.less_than.greater_than.imply.contains.apply(Eq[-4], Eq[-1])
         
    Eq << Eq.intermediate_value.subs(Eq.intermediate_value.rhs, Eq[-1].lhs)
    
    Eq <<= Eq[-1] & Eq[-2] 
    
    Eq << Eq[-1].split()
    
    Eq << Eq[-1] * (b - a)
    
    Eq << Eq[-1].this.function.rhs.ratsimp().reversed
    
    
if __name__ == '__main__':
    prove(__file__)

