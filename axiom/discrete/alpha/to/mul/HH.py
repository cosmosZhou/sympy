from util import *

from axiom.discrete.H.to.add.definition import H

from axiom.discrete.imply.gt_zero.alpha import alpha


def reverse(x):
    n = x.shape[0]
    i = x.generate_var(integer=True, free_symbols='i')
    return Lamda[i:n](x[n - 1 - i])


@apply
def apply(x):
    n = x.shape[0]
    assert x.is_positive
    assert n >= 2
    return Equal(alpha(reverse(x)), H(x[:n]) / H(x[:n - 1]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(real=True, positive=True, shape=(oo,))
#     x = Symbol.x(real=True, shape=(oo,))
    n = Symbol(domain=Range(2, oo), given=False)

    Eq << apply(x[:n])

    Eq.initial = Eq[0].subs(n, 2)

    Eq << Eq.initial.this.find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.lhs.apply(discrete.alpha.matrix)

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(alpha).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << Eq[-1].this.find(H).defun()

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << discrete.imply.ne_zero.alpha.apply(reverse(x[:n]))

    Eq << algebra.ne_zero.eq.imply.eq.inverse.apply(Eq[-1], Eq[0])

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.infer.imply.eq.induct.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

# created on 2020-09-27
# updated on 2020-09-27
