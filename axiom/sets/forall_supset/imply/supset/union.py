from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Supset, Or
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import LAMBDA, UNION
from axiom import algebre, sets
from sympy.core.symbol import dtype


@apply
def apply(given):
    eq, *limits = axiom.forall_supset(given)
    lhs, rhs = eq.args
    
    return Supset(UNION(lhs, *limits).simplify(), UNION(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(nargs=(), shape=(), etype=dtype.integer)
    g = Function.g(nargs=(), shape=(), etype=dtype.integer)
    
    Eq << apply(ForAll[i:n](Supset(f(i), g(i))))
    
    Eq << Eq[0].reversed
    
    Eq << sets.forall_subset.imply.subset.union.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].reversed

if __name__ == '__main__':
    prove(__file__)

