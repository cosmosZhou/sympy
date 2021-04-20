from sympy import *
from axiom.utility import prove, apply


@apply
def apply(given, old, new): 
    assert old.is_symbol
    assert old.is_given is None
#    old should not be a inductive symbol in mathematical induction proof!
    assert new in given.domain_defined(old)
    return given._subs(old, new)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(real=True, shape=())
    
    x = Symbol.x(real=True, positive=True, shape=(n,))    
    y = Symbol.y(real=True, positive=True, shape=(n,))
    
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(f(x) * a > b, x, y)
    
    Eq << Eq[0].subs(x, y)
    
    
if __name__ == '__main__':
    prove()
