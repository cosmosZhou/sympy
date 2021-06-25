from util import *


@apply
def apply(given, *, cond=None):
    p, q = given.of(Suffice)
        
    return Suffice(p & cond, q), Suffice(p & cond.invert(), q)


@prove
def prove(Eq):
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    Eq << apply(Suffice(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)
    
    Eq <<= Eq[-1] & Eq[-2]
    

        
if __name__ == '__main__':
    run()

from . import ou
from . import et
