from sympy import *
from axiom.utility import prove, apply


@apply(imply=True)
def apply(given, old, new): 
    assert given.is_Equality    
    assert old.is_symbol
    assert old.is_given is None    
    assert new in given.domain_defined(old)
    return given._subs(old, new)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(real=True, shape=(n,))
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Equality(f(x) * a, b), x, y)
    
    Eq << Eq[0].subs(x, y)
    
    
if __name__ == '__main__':
    prove(__file__)
