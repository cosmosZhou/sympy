from sympy import *
from axiom.utility import prove, apply


def is_continuous(f, a, b, x=None, xi=None): 
    if xi is None:
        xi = Symbol('xi', real=True)
        
    if x is None:
        x = Symbol('x', real=True)
        
    return ForAll[xi:a:b](Equality(Limit[x:xi](f(x)), f(xi)))


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

    y = Symbol.y(real=True)
    return ForAll(Exists(Equality(f, y), (z, a, b)), (y, MIN(f, (z, a, b)), MAX(f, (z, a, b))))               


@prove(surmountable=False)
def prove(Eq): 

    a = Symbol.a(real=True)
    b = Symbol.b(real=True, domain=Interval(a, oo, left_open=True))
    f = Function.f(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b))


if __name__ == '__main__':
    prove(__file__)

