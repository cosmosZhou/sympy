from util import *


@apply
def apply(self):
    assert self.is_sigma
    x, (k,) = self.args
    n = x.shape[0]
    assert k >= 2
    n -= 1
    return Equal(self, x[n] * sigma[k - 1](x[:n]) + sigma[k](x[:n]))


from axiom.discrete.sigma.to.add.recurrent import sigma


@prove(surmountable=False)
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(oo,))
    k = Symbol.k(domain=Range(2, n + 1))

    Eq << apply(sigma[k](x[:n + 1]))

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.dissect, cond=CartesianSpace(Range(0, n), k))

    Eq << Eq[-1].this.find(Complement).apply(sets.complement.to.conditionset)


if __name__ == '__main__':
    run()

