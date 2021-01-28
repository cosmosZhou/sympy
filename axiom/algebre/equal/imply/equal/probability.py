from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Or
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import algebre, sets
from sympy.stats.symbolic_probability import Probability


@apply(imply=True)
def apply(given):
    lhs, rhs = axiom.is_Equal(given)
    assert lhs.is_random 
    assert rhs.is_random
    return Equality(Probability(lhs), Probability(rhs))    


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    p = Symbol.p(shape=(n,), integer=True, random=True)
    q = Symbol.q(shape=(n,), integer=True, random=True)
    
    Eq << apply(Equality(p[i], q[i]))
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    prove(__file__)

