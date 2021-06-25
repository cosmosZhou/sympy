from util import *


@apply
def apply(self):
    function, (n, _n, (a, b)) = self.of(Sum[Tuple[Equal[Expr % 2, 0], Range]])
    assert n == _n
    return Equal(self, Sum[n:(a + 1) // 2:(b + 1) // 2](function._subs(n, 2 * n)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True)

    f = Symbol.f(shape=(oo,), real=True)

    a = Symbol.a(integer=True)

    b = Symbol.b(integer=True)

    Eq << apply(Sum[n:Equal(n % 2, 0):Range(a, b + 1)](f[n]))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.bool)

    S = Symbol.S(imageset(n, 2 * n, Eq[-1].rhs.limits_cond))

    Eq << S.this.definition

    Eq << algebra.sum.bool.apply(Sum[n:S](f[n]))

    Eq << Eq[-1].this.lhs.limits[0][1].definition

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.function.args[1].arg.rhs.definition

    Eq << Eq[-1].this.lhs.function.args[1].arg.apply(sets.et.to.contains.split.is_even)


if __name__ == '__main__':
    run()

