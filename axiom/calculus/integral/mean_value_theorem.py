from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, calculus, sets


@apply
def apply(given):
    assert given.is_ForAll
    assert given.function.is_Equal
    assert given.function.lhs.is_Limit
    f, (z, xi, direction) = given.function.lhs.args
    assert direction == 0
    assert len(given.limits) == 1
    limit = given.limits[0]
    _xi, a, b = limit
    assert xi == _xi
    _f = f._subs(z, xi)
    assert given.function.rhs == _f

    return Exists(Equal(Integral(f, (z, a, b)), (b - a) * _f), limit)


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
    
    Eq << algebra.imply.forall_le.min.apply(m.definition)
    
    Eq << algebra.forall_le.imply.le.integral.apply(Eq[-1]) 
    
    Eq << Eq[-1].subs(Eq.min.reversed) / (b - a)
    
    Eq << algebra.imply.forall_ge.max.apply(M.definition)
    
    Eq << calculus.forall_ge.imply.ge.integral.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.max.reversed) / (b - a)
    
    Eq <<= sets.le.ge.imply.contains.apply(Eq[-4], Eq[-1])
    
    Eq << algebra.forall.imply.ou.subs.apply(Eq.intermediate_value, Eq.intermediate_value.rhs, Eq[-1].lhs)
    
    Eq << algebra.ou.imply.exists_ou.apply(Eq[-1], simplify=None)
    
    Eq << algebra.cond.exists.imply.exists_et.apply(Eq[-1], Eq[-3], simplify=None)
    
    Eq << algebra.exists_et.imply.exists.split.apply(Eq[-1]) 
    
    Eq << Eq[-1].this.function * (b - a)
    
    Eq << Eq[-1].this.function.rhs.ratsimp().reversed
    
    
if __name__ == '__main__':
    prove()

