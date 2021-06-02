
from util import *

import axiom






@apply
def apply(given, x):
    lhs, rhs = given.of(Equal)
    
    return Equal(Max(lhs, x).simplify(), Max(rhs, x).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    
    Eq << apply(Equal(x, y), z)    
    
    Eq << Eq[-1].subs(Eq[0])
        

if __name__ == '__main__':
    run()
