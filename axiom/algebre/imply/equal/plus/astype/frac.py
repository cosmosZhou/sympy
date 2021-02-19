from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(sub):
    y, x = axiom.is_Substract(sub)
    
    if y == ceiling(x):
        return Equality(sub, frac(-x))
    if x == floor(y):
        return Equality(sub, frac(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(ceiling(x) - x)
    
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.ceiling.astype.times)

    
if __name__ == '__main__':
    prove(__file__)
