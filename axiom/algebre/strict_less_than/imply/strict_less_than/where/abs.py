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

    Eq << algebre.imply.less_than.abs.single.apply(a, negate=True)
    
    Eq << algebre.less_than.strict_less_than.imply.strict_less_than.transit.apply(Eq[-1], Eq[0])

    
if __name__ == '__main__':
    prove(__file__)

