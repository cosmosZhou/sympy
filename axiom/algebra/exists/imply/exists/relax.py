from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, old, new):
    function, *limits = axiom.is_Exists(given)    
    assert len(limits) == 1
    limit = limits[0]
    assert len(limit) == 1
    _old = limits[0][0]
    assert old == _old
    assert old.domain in new.domain
    
    return Exists[new](function._subs(old, new))


@prove
def prove(Eq): 
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(domain=Interval(a, b, right_open=True))
    y = Symbol.y(domain=Interval(a, b))
    z = Symbol.z(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(Exists[x](f(x) > 0), x, y)
    
    Eq << Eq[1].limits_subs(y, z)
    
    Eq << algebra.exists.given.exists.subs.apply(Eq[-1], z, x)

if __name__ == '__main__':
    prove()

