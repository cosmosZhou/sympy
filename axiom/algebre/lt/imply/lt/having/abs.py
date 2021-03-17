from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, negate=False):
    x, M = axiom.is_StrictLessThan(given)
    x = axiom.is_Abs(x)
    if negate:
        x = -x
    return StrictLessThan(x, M)


@prove
def prove(Eq):
    M = Symbol.M(real=True)
    a = Symbol.a(real=True)
    
    Eq << apply(StrictLessThan(abs(a), M), negate=True)

    Eq << algebre.imply.le.abs.single.apply(a, negate=True)
    
    Eq << algebre.le.lt.imply.lt.transit.apply(Eq[-1], Eq[0])

    
if __name__ == '__main__':
    prove(__file__)

