from axiom.utility import prove, apply
from sympy import Equality, Subset
from sympy import Symbol, ForAll, Slice, UNION
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Subset(given)
    
    return Subset(UNION(lhs, *limits).simplify(), UNION(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(nargs=(), shape=(), etype=dtype.real)
    g = Function.g(nargs=(), shape=(), etype=dtype.real)
    
    Eq << apply(Subset(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebre.cond.imply.forall.restrict, (i, 0, n))
    
    Eq << sets.forall_subset.imply.subset.union.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    prove(__file__)

