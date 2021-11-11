from util import *


@apply
def apply(self):
    function, (n, _n, (a, b)) = self.of(Sum[Tuple[Equal[Expr % 2, 0], Range]])
    assert n == _n
    return Equal(self, Sum[n:(a + 1) // 2:(b + 1) // 2](function._subs(n, 2 * n)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Sum[n:Equal(n % 2, 0):Range(a, b + 1)](f[n]))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.bool)

    S = Symbol(imageset(n, 2 * n, Eq[-1].rhs.limits_cond))
    Eq << S.this.definition

    Eq << algebra.sum.bool.apply(Sum[n:S](f[n]))

    Eq << Eq[-1].this.lhs.limits[0][1].definition

    Eq << Eq[-1].this.lhs.apply(algebra.sum.imageset)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.args[1].arg.rhs.definition

    Eq << Eq[-1].this.lhs.expr.args[1].arg.apply(sets.et.to.el.split.is_even)


if __name__ == '__main__':
    run()

# created on 2018-05-28
# updated on 2018-05-28
