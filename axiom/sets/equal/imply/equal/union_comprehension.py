from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Equal(given)
    
    return Equality(UNION(lhs, *limits).simplify(), UNION(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    f = Function.f(nargs=(), shape=(), etype=dtype.integer)
    g = Function.g(nargs=(), shape=(), etype=dtype.integer)
    
    Eq << apply(Equality(f(i), g(i)), (i, 0, n))
    
    Eq << Eq[0].forall((i,))
    Eq << sets.forall_equal.imply.equal.union_comprehension.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

