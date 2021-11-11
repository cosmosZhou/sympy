from util import *


@apply
def apply(self):
    (function, *sgm_limits), *limits = self.of(Lamda[Sum])
    rhs = Sum(Lamda(function, *limits).simplify(), *sgm_limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n, n), real=True)
    Eq << apply(Lamda[i:n](Sum[j:n](x[j, i])))
    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()
# created on 2019-10-21
# updated on 2019-10-21
