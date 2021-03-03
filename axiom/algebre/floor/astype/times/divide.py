from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self):
    div = axiom.is_Floor(self)
    n, d = axiom.is_Divide(div)

    return Equality(self, (n - n % d) / d)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(n // d)
    
    Eq << Eq[0].this.rhs.args[1].args[1].args[1].definition
    
if __name__ == '__main__':
    prove(__file__)

