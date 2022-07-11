from util import *


@apply(given=None)
def apply(contains, w):
    (x, i), domain = contains.of(Element[Indexed])
    [n] = w.shape
    return Infer(And(Equal(Sum[i:n](w[i]), 1), All[i:n]((w[i] >= 0) & contains)), Element(Sum[i:n](w[i] * x[i]), domain))

@prove
def prove(Eq):
    from axiom import algebra, sets

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    w, x = Symbol(real=True, shape=(oo,))
    Eq << apply(Element(x[i], Interval(a, b)), w[:n])

    Eq.initial = Eq[0].subs(n, 1)

    Eq << algebra.infer_et.given.infer.subs.apply(Eq.initial, index=0)

    Eq.induct = Eq[0].subs(n, n + 1)

    #Eq << Eq.induct.this.find(Equal[~Sum]).apply(algebra.sum.to.add.pop_back)
    #Eq << Eq[-1].this.find(All).apply(algebra.all.imply.et.split, cond={n})
    Eq << Eq.induct.this.find(All).apply(algebra.all_et.imply.et.all)

    Eq << Eq[-1].this.find(Element[~Sum]).apply(algebra.sum.to.add.pop_back)

    Eq.lt, Eq.ge = algebra.cond.given.et.infer.split.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.rhs.apply(algebra.infer.fold, 1, swap=True)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.eq_sum.ge.all_ge_zero.imply.eq.all_is_zero.squeeze)

    Eq << Eq[-1].this.find(All[Element]).apply(algebra.all.imply.cond.subs, i, n)

    Eq << algebra.infer_et.given.infer.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(algebra.all_is_zero.imply.sum_is_zero.mul, x)

    Eq << algebra.infer_et.given.infer.subs.apply(Eq[-1], index=1)

    Eq << Eq.lt.this.rhs.apply(algebra.infer.fold, 2)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.find(Equal[~Sum]).apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.lhs.apply(algebra.eq.lt.imply.eq.div, ret=0)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold, 2)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.apply(algebra.infer.fold, slice(0, 2))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.imply.all_et, simplify=None)

    Eq << Eq[-1].this.lhs.find(And).apply(algebra.lt.ge.imply.ge.div, ret=1)

    Eq << Eq[-1].this.apply(algebra.infer.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold, slice(0, 2), swap=True)

    Eq << Eq[-1].this.rhs.rhs.lhs.apply(sets.lt.ge.imply.el.interval)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold, 0, swap=True)

    Eq << Eq[-1].this.find(All & All).apply(algebra.all.all.imply.all_et)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.flatten)

    w_ = Symbol('w', Lamda[i:n](w[i] / (1 - w[n])))
    Eq << (w_[i].this.definition * (1 - w[n])).reversed

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum[Mul]).apply(algebra.sum.to.mul)

    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], w[:n], w_)

    Eq << algebra.cond.imply.infer.apply(Eq[-1], cond=Eq[-2].rhs.lhs)

    Eq << Eq[-1].this.apply(algebra.infer.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.imply.infer.et)

    Eq << Eq[-1].this.rhs.rhs.apply(sets.el.el.el.imply.el.interval)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.rhs.find(Sum).simplify()

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
# created on 2020-05-31
