from util import *


@apply
def apply(self):
#     ((x, _i), x_means), (i, n) = self.of(Sum[(Indexed - Basic) ** 2, Tuple[0, Expr]])        
#     ((_x, _j), (j, _n)), __n = x_means.of(Sum[Indexed, Tuple[0, Expr]] / Expr)
    
    ((x, _i), (((_x, _j), (j, _n)), __n)), (i, n) = self.of(Sum[(Indexed - Sum[Indexed, Tuple[0, Expr]] / Expr) ** 2, Tuple[0, Expr]])
    
    assert i.is_integer and j.is_integer
    assert _i == i and _j == j
    assert _n == n and __n == n and _x == x

    if j == i:
        j = self.generate_var(excludes={i}, integer=True, var='j')

    return Equal(self, Sum[j:i, i:n]((x[i] - x[j]) ** 2) / n)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True, shape=(oo,))

    Eq << apply(Sum[i:n]((x[i] - Sum[j:n](x[j]) / n) ** 2))

    Eq << Eq[-1].this.lhs.function.expand()

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Pow, Sum).limits_subs(j, i)

    Eq << Eq[-1].this.find(Sum[2]).limits_subs(j, i)

    Eq << Eq[-1].this.lhs.find(Mul).args[2].apply(algebra.square.to.add.st.sum)

    Eq << Eq[-1].this.lhs.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Sum, Pow).apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1] * n

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[2].apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.args[1].doit()

    Eq << Eq[-1].this.rhs.args[1].limits_subs(j, i)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.push_front)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)


if __name__ == '__main__':
    run()

