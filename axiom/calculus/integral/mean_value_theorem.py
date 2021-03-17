from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebre, calculus, sets


@apply
def apply(given):
    assert given.is_ForAll
    assert given.function.is_Equality
    assert given.function.lhs.is_Limit
    f, (z, xi, direction) = given.function.lhs.args
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
    given = calculus.integral.intermediate_value_theorem.is_continuous(f, a, b)
    
    z = given.lhs.args[1][0]

    Eq << apply(given)
    
    m = Symbol.m(MIN(f(z), (z, a, b)))
    M = Symbol.M(MAX(f(z), (z, a, b)))
    
    Eq.min = m.this.definition
    Eq.max = M.this.definition
    
    Eq << axiom.calculus.integral.intermediate_value_theorem.apply(given)
    
    Eq.intermediate_value = Eq[-1].this.limits[0][2].subs(Eq.max.reversed).this.limits[0][1].subs(Eq.min.reversed)
    
    Eq << algebre.imply.forall_le.min.apply(m.definition)
    
    Eq << algebre.forall_le.imply.le.integrate.apply(Eq[-1]) 
    
    Eq << Eq[-1].subs(Eq.min.reversed) / (b - a)
    
    Eq << algebre.imply.forall_ge.max.apply(M.definition)
    
    Eq << calculus.forall_ge.imply.ge.integrate.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.max.reversed) / (b - a)
    
    Eq <<= sets.le.ge.imply.contains.apply(Eq[-4], Eq[-1])
         
    Eq << Eq.intermediate_value.subs(Eq.intermediate_value.rhs, Eq[-1].lhs)
    
    Eq <<= Eq[-1] & Eq[-2] 
    
    Eq << algebre.et.imply.cond.apply(Eq[-1])
    
    Eq << Eq[-1] * (b - a)
    
    Eq << Eq[-1].this.function.rhs.ratsimp().reversed
    
    
if __name__ == '__main__':
    prove(__file__)

