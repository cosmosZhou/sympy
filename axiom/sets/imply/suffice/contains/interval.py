from util import *


@apply(given=None)
def apply(contains, w):
    (x, i), domain = contains.of(Contains[Indexed])
    [n] = w.shape
    return Suffice(And(Equal(Sum[i:n](w[i]), 1), All[i:n]((w[i] >= 0) & contains)), Contains(Sum[i:n](w[i] * x[i]), domain))

@prove
def prove(Eq):
    from axiom import algebra, sets

    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    w = Symbol.w(real=True, shape=(oo,))
    x = Symbol.x(real=True, shape=(oo,))
    Eq << apply(Contains(x[i], Interval(a, b)), w[:n])

    Eq.initial = Eq[0].subs(n, 1)

    Eq << algebra.suffice_et.given.suffice.subs.apply(Eq.initial, index=0)

    Eq.induct = Eq[0].subs(n, n + 1)

    #Eq << Eq.induct.this.find(Equal[~Sum]).apply(algebra.sum.to.add.pop_back)
    #Eq << Eq[-1].this.find(All).apply(algebra.all.imply.et.split, cond={n})
    Eq << Eq.induct.this.find(All).apply(algebra.all_et.imply.et.all)

    Eq << Eq[-1].this.find(Contains[~Sum]).apply(algebra.sum.to.add.pop_back)

    Eq.lt, Eq.ge = algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.rhs.apply(algebra.suffice.fold, 1, swap=True)

    Eq << Eq[-1].this.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.eq_sum.ge.all_is_nonnegative.imply.eq.all_is_zero.squeeze)

    Eq << Eq[-1].this.find(All[Contains]).apply(algebra.all.imply.cond.subs, i, n)

    Eq << algebra.suffice_et.given.suffice.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(algebra.all_is_zero.imply.sum_is_zero.mul, x)

    Eq << algebra.suffice_et.given.suffice.subs.apply(Eq[-1], index=1)

    Eq << Eq.lt.this.rhs.apply(algebra.suffice.fold, 2)

    Eq << Eq[-1].this.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.find(Equal[~Sum]).apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.lhs.apply(algebra.et.imply.et.invoke, algebra.eq.lt.imply.eq.div)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.fold, 2)

    Eq << Eq[-1].this.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.apply(algebra.suffice.fold, slice(0, 2))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.imply.all_et, simplify=None)

    Eq << Eq[-1].this.lhs.find(And).apply(algebra.et.imply.et.invoke, algebra.lt.ge.imply.ge.div, ret=1)

    Eq << Eq[-1].this.apply(algebra.suffice.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.fold, slice(0, 2), swap=True)

    Eq << Eq[-1].this.rhs.rhs.lhs.apply(sets.lt.ge.imply.contains.interval)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.fold, 0, swap=True)

    Eq << Eq[-1].this.find(All & All).apply(algebra.all.all.imply.all_et)

    Eq << Eq[-1].this.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.flatten)

    w_ = Symbol.w(Lamda[i:n](w[i] / (1 - w[n])))
    Eq << (w_[i].this.definition * (1 - w[n])).reversed

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum[Mul]).apply(algebra.sum.to.mul)

    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], w[:n], w_)

    Eq << algebra.cond.imply.suffice.apply(Eq[-1], cond=Eq[-2].rhs.lhs)

    Eq << Eq[-1].this.apply(algebra.suffice.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.imply.suffice.et)

    Eq << Eq[-1].this.rhs.rhs.apply(sets.contains.contains.contains.imply.contains.interval)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.rhs.find(Sum).simplify()

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()