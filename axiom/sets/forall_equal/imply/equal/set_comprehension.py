from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, ForAll, Slice, Or
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval, FiniteSet
from sympy.concrete.expr_with_limits import LAMBDA, UNION
from axiom import algebre, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo


@apply
def apply(given):
    eq, *limits = axiom.forall_equal(given)
    lhs, rhs = eq.args
    
    return Equality(UNION(FiniteSet(lhs), *limits).simplify(), UNION(FiniteSet(rhs), *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Symbol.f(shape=(oo,), etype=dtype.integer)
    g = Symbol.g(shape=(oo,), etype=dtype.integer)
    
    Eq << apply(ForAll[i:n](Equality(f[i], g[i])))
    
    Eq << Eq[0].apply(sets.equal.imply.equal.set, simplify=False)
    
    Eq << sets.forall_equal.imply.equal.union_comprehension.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

