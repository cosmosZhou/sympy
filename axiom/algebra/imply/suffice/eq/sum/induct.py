from util import *


@apply
def apply(sgm):
    fx, (x, X) = sgm.of(Sum)

    (a, i), (_i, n) = X.of(Cup[FiniteSet[Indexed], Tuple[0]])
    assert _i == i
    j = sgm.generate_var(excludes=i, var='j', integer=True)

    return Suffice(All[j:i, i:n](Unequal(a[i], a[j])), Equal(sgm, Sum[i:n](fx._subs(x, a[i]))))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    X = Symbol(etype=dtype.real)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    s = a[:n].set_comprehension()
    Eq << apply(Sum[x:s](f(x)))

    Eq.initial = Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.all_ne.imply.eq.sum, Eq[0].rhs.lhs)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.eq.transposition, rhs=0)

    Eq << Eq[-1].this.lhs.args[0].reversed

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[0], cond=Eq[-1].lhs.args[1])

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.add)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.add.to.sum.limits.push_back)

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)
    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
