from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply(imply=True)
def apply(expr, *limits):
    return LessThan(abs(UNION(expr, *limits)), Sum(abs(expr), *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True)
    A = Symbol.A(shape=(oo,), etype=dtype.integer)
    Eq << apply(A[k], (k, 0, n + 1))

    Eq << Eq[0].subs(n, 1)
    
    Eq << Eq[-1].doit(deep=True)

    Eq << sets.imply.less_than.union.apply(*Eq[-1].lhs.arg.args)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.arg.bisect(Slice[-1:])

    Eq << sets.imply.less_than.union.apply(*Eq[-1].lhs.arg.args)

    Eq << algebre.less_than.less_than.imply.less_than.subs.apply(Eq[-1], Eq[0])

    Eq << Eq[3].this.rhs.bisect(Slice[-1:])
    
    Eq << Eq[3].induct(imply=True)

    Eq << algebre.condition.sufficient.imply.condition.induction.apply(Eq[1], Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove(__file__)

