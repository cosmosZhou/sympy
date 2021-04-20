from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    div = axiom.is_Floor(self)
    n, d = axiom.is_Divide(div)

    q = 0
    m = 0
    for arg in axiom.is_Add(n):
        if arg == d:
            q += 1
            continue
        elif arg.is_Mul:
            try:
                i = arg.args.index(d)
                args = [*arg.args]
                del args[i]
                q += Mul(*args)
                continue
            except:
                ...
                
        m += arg                
  
    return Equal(self, m // d + q)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    d = Symbol.d(integer=True)
    k = Symbol.k(integer=True)
    Eq << apply((x + d * k - 1 - d) // d)
    
    Eq << Eq[0].this.lhs.apply(algebra.floor.to.mul.divide)
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.apply(algebra.floor.to.mul.divide)
    
    Eq << Eq[-1].this.rhs.expand()

    
if __name__ == '__main__':
    prove()

