from util import *

from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(self):
    assert self.is_alpha
    x = self.arg

    assert x.is_positive
    assert x.shape[0].is_finite

    return Equal(self, H(x) / K(x))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(integer=True)

    Eq.hypothesis = apply(alpha(x[:n + 1]))

    Eq.n2 = Suffice(n >= 2, Eq.hypothesis, plausible=True)

    Eq << Eq.n2.this.apply(algebra.suffice.to.all)

    _n = Symbol.n(domain=Range(2, oo))

    Eq << discrete.alpha.to.mul.HK.induct.apply(alpha(x[:_n + 1]))

    Eq << algebra.cond.imply.all.apply(Eq[-1], _n)

    Eq.n1 = Suffice(Equal(n, 1), Eq.hypothesis, plausible=True)

    Eq << Eq.n1.this.apply(algebra.suffice.subs)

    Eq << Eq[-1].this.rhs.subs(alpha(x[:2]).this.defun(),
                               alpha(x[1]).this.defun(),
                               H(x[:2]).this.defun(),
                               K(x[:2]).this.defun())

    Eq << Eq[-1].this.rhs.rhs.apart(x=x[1])

    Eq.n1 = algebra.suffice.suffice.imply.suffice.ou.apply(Eq.n1, Eq.n2)

    Eq.n0 = Suffice(Equal(n, 0), Eq.hypothesis, plausible=True)

    Eq << Eq.n0.this.apply(algebra.suffice.subs)

    Eq << Eq[-1].this.rhs.subs(alpha(x[0]).this.defun(),
                               H(x[0]).this.defun(),
                               K(x[0]).this.defun())

    Eq << algebra.suffice.suffice.imply.suffice.ou.apply(Eq.n1, Eq.n0)

    Eq << Eq[-1].this.apply(algebra.suffice.to.all, wrt=n)

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

