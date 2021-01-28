from axiom.utility import prove, apply
from sympy import Symbol
from sympy import ForAll, Exists
from sympy.sets.sets import Interval
from sympy.core.relational import Equality
from sympy.concrete.limits import limits_condition


@apply(imply=True, simplify=False)
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

