from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self):
    div = axiom.is_Floor(self)
    n, d = axiom.is_Divide(div)

    q = 0
    m = 0
    for arg in axiom.is_Plus(n):
        if arg == d:
            q += 1
            continue
        elif arg.is_Times:
            try:
                i = arg.args.index(d)
                args = [*arg.args]
                del args[i]
                q += Times(*args)
                continue
            except:
                ...
                
        m += arg                
  
    return Equality(self, m // d + q)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    d = Symbol.d(integer=True)
    k = Symbol.k(integer=True)
    Eq << apply((x + d * k - 1 - d) // d)
    
    Eq << Eq[0].this.lhs.apply(algebre.floor.astype.times.divide)
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1].this.rhs.apply(algebre.floor.astype.times.divide)
    
    Eq << Eq[-1].this.rhs.expand()

    
if __name__ == '__main__':
    prove(__file__)

