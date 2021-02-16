from sympy import *
from axiom.utility import prove, apply
import axiom
from sympy.concrete.limits import limits_condition


@apply(imply=True, simplify=False)
def apply(given):
    fn, *limits = axiom.exists_equal(given)
    x, y = fn.args
    cond = limits_condition(limits)
    return cond._subs(x, y)


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    k = Symbol.k(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Exists[x:S](Equal(x, y)))
    
    Eq << Eq[0].simplify()

    
if __name__ == '__main__':
    prove(__file__)

