from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
# P is condition set;


@apply
def apply(y, x=None):
    U = y.universalSet
    
    if x is None:
        x = y.generate_free_symbol(**y.type.dict)
    return ForAll[x:U // y.set](Unequal(x, y))


@prove
def prove(Eq):
    y = Symbol.y(complex=True)
    Eq << apply(y)
    
    Eq << algebre.forall.given.ou.apply(Eq[0])

if __name__ == '__main__':
    prove(__file__)

