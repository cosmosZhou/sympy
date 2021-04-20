from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(expr, *limits):
    return LessEqual(abs(UNION(expr, *limits)), Sum(abs(expr), *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)
    A = Symbol.A(shape=(oo,), etype=dtype.integer)
    Eq << apply(A[k], (k, 0, n + 1))

    Eq << Eq[0].subs(n, 1)
    
    Eq << Eq[-1].this.lhs.doit(deep=True)
    
    Eq << Eq[-1].this.rhs.doit(deep=True)

    Eq << sets.imply.le.union.apply(*Eq[-1].lhs.arg.args)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.arg.bisect(Slice[-1:])

    Eq << sets.imply.le.union.apply(*Eq[-1].lhs.arg.args)

    Eq << algebra.le.le.imply.le.subs.apply(Eq[-1], Eq[0])

    Eq << Eq.induct.this.rhs.bisect(Slice[-1:])
    
    Eq << Eq.induct.induct(imply=True)

    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq[1], Eq[-1], n=n, start=1)

    
if __name__ == '__main__':
    prove()

