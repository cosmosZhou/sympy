from sympy import *
from axiom.utility import prove, apply
from sympy.concrete.limits import limits_condition


@apply(simplify=False)
def apply(limits):
    return ForAll(limits_condition(limits), *limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    f = Exists[x: Interval(0, n)](Equality(x * 2, 1)) 

    Eq << apply(f.limits)
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove(__file__)

