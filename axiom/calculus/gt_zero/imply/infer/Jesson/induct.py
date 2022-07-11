from util import *


@apply
def apply(is_positive, x=None, w=None, i=None, n=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    domain = x_.domain
    assert domain.left_open and domain.right_open
    if x is None:
        x = Symbol(shape=(oo,), domain=domain)

    if w is None:
        w = Symbol(shape=(oo,), real=True)

    if i is None:
        i = Symbol(integer=True)

    if n is None:
        n = Symbol(integer=True, positive=True)

    assert x.domain_assumed == domain
    return Infer(Equal(Sum[i:n](w[i]), 1) & All[i:n](w[i] >= 0), GreaterEqual(Sum[i:n](w[i] * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](w[i] * x[i]))))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x = Symbol(domain=domain)
    w = Symbol(shape=(oo,), real=True)
    f = Function(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, w=w, n=n)

    Eq.initial = Eq[1].subs(n, 1)

    Eq << Eq.initial.this.lhs.apply(algebra.eq.cond.imply.cond.subs, ret=0)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.this.rhs.find(Sum).apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-1].this.find(f[~Sum]).apply(algebra.sum.to.add.pop_back)

    Eq.lt, Eq.ge = algebra.cond.given.et.infer.split.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.eq_sum.ge.all_ge_zero.imply.eq.all_is_zero.squeeze)

    Eq << algebra.infer_et.given.infer.subs.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.et.imply.cond, index=1)

    i = Eq[-1].lhs.variable
    fxi = Eq[-1].rhs.find(Sum, f)
    Eq << Eq[-1].lhs.this.apply(algebra.all_is_zero.imply.sum_is_zero.mul, Lamda[i:n](fxi))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    x = fxi.arg.base
    Eq << Eq[-1].lhs.this.apply(algebra.all_is_zero.imply.sum_is_zero.mul, x)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << Eq.lt.this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond={n})

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.find(Less) - w[n]

    Eq << Eq[-1].this.apply(algebra.infer.fold, index=1)

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.eq.imply.eq.div, simplify=None, ret=0)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.all.imply.et.split, cond={n})

    Eq << Eq[-1].this.apply(algebra.infer.fold)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold, index=slice(0, 2))

    Eq << Eq[-1].this.find(And).apply(algebra.cond.all.imply.all_et, simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.gt_zero.ge.imply.ge.div, ret=0)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    w_ = Symbol('w', Lamda[i:n](w[i] / (1 - w[n])))
    Eq << w_[i].this.definition * (1 - w[n])

    Eq << Eq[-1].reversed

    Eq << algebra.cond.given.et.subs.apply(Eq[-3], *Eq[-1].args, simplify=None)

    Eq << Eq[-1].this.find(~GreaterEqual & Equal).apply(algebra.cond.imply.all.domain_defined, wrt=i)

    Eq << Eq[-1].this.find(Add[~Sum]).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find(Add[~Sum]).apply(algebra.sum.to.mul)

    Eq.induct1 = Eq[-1].this.lhs.apply(sets.lt.ge.imply.el.interval)

    Eq << algebra.cond.imply.cond.subs.apply(Eq[1], w[:n], w_)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.find(~Sum >= f).simplify()

    Eq << Eq[-1].this.find(f[~Sum]).simplify()

    Eq << algebra.cond.imply.infer.apply(Eq[-1], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.apply(algebra.infer_infer.imply.infer_infer.et)

    Eq <<  Eq[-1].this.find(And[~Element]).apply(sets.el_interval.imply.lt)

    Eq << Eq[-1].this.find(And[Less]).apply(algebra.lt.ge.imply.ge.mul)

    Eq.hypothesis = Eq[-1].this.find(GreaterEqual[Mul]) + w[n] * f(x[n])

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.find(Greater).apply(algebra.cond.imply.all, Eq[-1].find(Derivative).variable)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Element(x[n], domain, plausible=True)

    Eq << algebra.cond.imply.infer.apply(Eq[-1], cond=Eq[-2].lhs)

    Eq <<= Eq[-3] & Eq[-1]

    Eq.suffices = Eq[-1].this.rhs.apply(algebra.cond.imply.infer, cond=Eq.induct1.rhs.lhs)

    Eq << Element(x[i], domain, plausible=True)

    Eq << algebra.cond.imply.infer.apply(Eq[-1], cond=Eq.induct1.rhs.lhs)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.cond.all.imply.all_et, simplify=None)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[-1].this.rhs.apply(sets.eq_sum.all.imply.el.mean)

    Eq << algebra.cond.imply.infer.apply(Eq[-1], cond=Eq.suffices.lhs)

    Eq <<= Eq.suffices & Eq[-1]

    Eq << Eq[-1].this.rhs.rhs.apply(calculus.el.el.el.all_gt_zero.imply.ge.Jesson, swap=True)

    Eq << Eq[-1].this.find(Sum[Mul]).simplify()

    Eq << Eq[-1].this.find(Sum[Mul, Tuple[0]]).simplify()

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.find(GreaterEqual & GreaterEqual).apply(algebra.ge.ge.imply.ge.transit)

    Eq << Infer(Eq[1], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
# created on 2020-06-01
