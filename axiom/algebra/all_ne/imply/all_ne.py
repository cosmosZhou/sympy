from util import *


@apply
def apply(all_ne):
    (xi, xj), (j, S[0], i), (S[i], S[0], n) = all_ne.of(All[Unequal])
    if xi._has(j):
        xi, xj = xj, xi
    x = Lamda[i:n](xi).simplify()
    assert xj == x[j]
    
    return All[j:Range(n) - {i}, i:n](Unequal(xi, xj))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    i, j = Symbol(integer=True)
    Eq << apply(All[j:i, i:n](Unequal(x[i], x[j])))

    k = Symbol(integer=True)
    Eq << Eq[0].limits_subs(j, k).limits_subs(i, j).limits_subs(k, i)

    Eq << Eq[-1].this.apply(algebra.all.limits.swap.intlimit)

    Eq << Eq[-1].this.expr.reversed

    Eq << algebra.all.all.imply.all.limits_union.apply(Eq[-1], Eq[0])

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq << Element(i, Range(-1, n + 1)).this.apply(sets.el_range.imply.eq.union.to.complement)

    Eq << Eq[-1].this.lhs.apply(sets.el.given.el.restrict, Range(0, n))

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << algebra.infer.imply.all.apply(Eq[-1])

    
    Eq << Eq[-1].this.expr.apply(algebra.ou.imply.all)
    
    


if __name__ == '__main__':
    run()
# created on 2022-01-24
# updated on 2022-01-28
