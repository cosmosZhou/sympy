from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom.algebre.equal.astype.exists.limit_definition import exists
from axiom import algebre


@apply
def apply(given, ε=None, δ=None):
    return exists(given, ε, δ)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True)
#     x = Symbol.x(real=True, shape=(n,))
    x = Symbol.x(integer=True)
    
    f = Function.f(real=True, shape=())
        
    x0 = Symbol.x0(real=True)
#     x0 = Symbol.x0(real=True, shape=(n,))
    
    x0 = oo
#     x0 = -oo
    
    a = Symbol.a(real=True)    
#     a = oo
#     a = -oo

    direction = '+-'
#     direction = '+'
    direction = '-'
    
    Eq << apply(Equal(Limit(f(x), x, x0, direction), a))
    
    Eq << algebre.equal.astype.exists.limit_definition.apply(Eq[0])
        
    Eq << algebre.condition.equivalent.imply.condition.transit.apply(Eq[0], Eq[-1])
    
    
if __name__ == '__main__':
    prove(__file__)
