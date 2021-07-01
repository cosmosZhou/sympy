from util import *
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    (x, _j), (j, n1) = given.of(All[Indexed >= 1, Tuple[1, Expr]])

    n = n1 - 1
    assert _j == j

    return GreaterEqual(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(All[i:1:n + 1](x[i] >= 1))

    Eq.case2, Eq.case1 = algebra.cond.given.suffice.split.apply(Eq[-1], cond=n >= 2)

    Eq << Eq.case1.this.lhs.apply(algebra.lt.to.eq.squeeze)

    Eq << Eq[-1].this.apply(algebra.suffice.subs)

    Eq << Eq[-1].this.find(K).defun()

    Eq << Eq[-1].this.find(K).defun()

    Eq << algebra.suffice.given.cond.apply(Eq[-1])

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], i, 1)

    _n = Symbol.n(domain=Range(2, oo))

    Eq << Eq[0].subs(n, _n)

    Eq << discrete.all_ge.imply.gt.K.apply(Eq[-1])

    Eq << Eq[-1].forall((_n,))

    Eq << Eq[-1].this.function.apply(algebra.gt.imply.ge.relax)

    Eq << algebra.suffice.given.all.apply(Eq.case2)


if __name__ == '__main__':
    run()

