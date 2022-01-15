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


@prove(proved=False)
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(oo,))
    k = Symbol(domain=Range(2, n + 1))

    Eq << apply(sigma[k](x[:n + 1]))

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.find(sigma).defun()

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond=CartesianSpace(Range(n), k))

    Eq << Eq[-1].this.find(Complement).apply(sets.complement.to.conditionset)


if __name__ == '__main__':
    run()

# created on 2020-11-18
