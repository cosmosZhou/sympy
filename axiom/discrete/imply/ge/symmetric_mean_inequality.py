from util import *


@apply
def apply(x, k=None):
    n = x.shape[0]
    if k is None:
        k = Symbol.k(integer=True)

    return All[k:1:n](GreaterEqual((sigma[k](x[:n]) / binomial(n, k)) ** (1 / k),
                                      (sigma[k + 1](x[:n]) / binomial(n, k + 1)) ** (1 / (k + 1))))


from axiom.discrete.sigma.to.add.recurrent import sigma


@prove(proved=False)
def prove(Eq):
    from axiom import algebra
    n = Symbol(domain=Range(2, oo), given=False)
    x = Symbol(real=True, positive=True, shape=(oo,))
    k = Symbol(integer=True)

    Eq << apply(x[:n], k)

    Eq.initial = Eq[0].subs(n, 2)

    Eq << Eq.initial.this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.doit)

    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.doit.outer)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.doit)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.split.slice.cartesianSpace.baseset)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.doit.outer)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.delete.condset)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.delete.condset)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1] * 2

    Eq << algebra.imply.ge_zero.square.apply(sqrt(x[0]) - sqrt(x[1]))

    Eq << algebra.ge_zero.imply.ge.apply(Eq[-1])

    k_ = Symbol.k(domain=Range(2, n))
    t = Function(eval=lambda k: (sigma[k](x[:n]) / binomial(n, k)) ** (1 / k), real=True)
    Eq << t(k_).this.defun()

    Eq << algebra.eq.imply.eq.pow.apply(Eq[-1], exp=k_)

    Eq << Eq[-1] * binomial(n, k_)

    Eq.s_k = Eq[-1].reversed

    Eq << t(k_ + 1).this.defun()

    Eq << algebra.eq.imply.eq.pow.apply(Eq[-1], exp=k_ + 1)

    Eq << Eq[-1] * binomial(n, k_ + 1)

    Eq.s_k1 = Eq[-1].reversed

    Eq << t(k_ - 1).this.defun()

    Eq << algebra.eq.imply.eq.pow.apply(Eq[-1], exp=k_ - 1)

    Eq << Eq[-1] * binomial(n, k_ - 1)

    Eq.s_k1_neg = Eq[-1].reversed

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], k, k_)

    Eq.hypothesis_k = Eq[-1].subs(t(k_).this.defun().reversed).subs(t(k_ + 1).this.defun().reversed)

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], k, k_ - 1)

    Eq.hypothesis_k_1 = Eq[-1].subs(t(k_).this.defun().reversed).subs(t(k_ - 1).this.defun().reversed)

    Eq << Eq[0].subs(n, n + 1)

    Eq << GreaterEqual(((sigma[k_](x[:n]) + x[n] * sigma[k_ - 1](x[:n])) / binomial(n, k_)) ** (1 / k_),
                       ((sigma[k_ + 1](x[:n]) + x[n] * sigma[k_](x[:n])) / binomial(n, k_ + 1)) ** (1 / (k_ + 1)), plausible=True)
    return
    Eq << Eq[-1].subs(Eq.s_k)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].subs(Eq.s_k1)

    Eq << Eq[-1].this.rhs.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].subs(Eq.s_k1_neg)


if __name__ == '__main__':
    run()

# created on 2020-11-05
