from sympy import *
from axiom.utility import prove, apply
import axiom
from sympy.concrete.limits import limits_cond


@apply(simplify=False)
def apply(given):
    fn, *limits = axiom.exists_eq(given)
    x, y = fn.args
    cond = limits_cond(limits)
    return cond._subs(x, y)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Exists[x:S](Equal(x, y)))
    
    Eq << Eq[0].simplify()

    
if __name__ == '__main__':
    prove()

