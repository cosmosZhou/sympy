from util import *

from axiom.discrete.imply.gt_zero.alpha import alpha
from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[0, Expr]])
    offset = _j - j
    if offset != 0:
        assert not offset._has(j)
        x = x[offset:]
    return Equal(alpha(x[:n]), H(x[:n]) / K(x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:0:n](x[i] > 0))

    x_ = Symbol('x', real=True, positive=True, shape=(oo,))
    Eq << discrete.alpha.to.mul.HK.st.gt_zero.apply(alpha(x_[:n]))

    Eq << Eq[-1].subs(x_[:n], x[:n])

    Eq << algebra.ou.imply.infer.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.simplify()
    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-09-20
