from util import *


@apply
def apply(n, m, b):
    i = Symbol.i(integer=True)

    return Equal(BlockMatrix(BlockMatrix(MatProduct[i:m](Swap(n, i, b[i])), ZeroMatrix(n)).T,
                             BlockMatrix(ZeroMatrix(n), 1)).T,
                             MatProduct[i:m](Swap(n + 1, i, b[i])))


@prove
def prove(Eq):
    from axiom import algebra, discrete
    n = Symbol.n(domain=Range(2, oo))
    m = Symbol.m(positive=True, integer=True, given=False)
    b = Symbol.b(integer=True, shape=(oo,), nonnegative=True)

    Eq << apply(n, m, b)

    Eq.initial = Eq[0].subs(m, 1)

    Eq.concatenate = discrete.matrix.elementary.swap.concatenate.apply(n)

    * _, i, j = Eq.concatenate.rhs.args
    Eq << Eq.concatenate.subs(i, 0).subs(j, b[0]).T

    Eq.induct = Eq[0].subs(m, m + 1)

    Eq << Eq.induct.this.rhs.split(Slice[-1:])

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq << Eq.concatenate.subs(i, m).subs(j, b[m]).T

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.expand()

    i = Eq[0].rhs.variable
    Eq << Eq[-1].this.rhs.args[0].arg.args[0].limits_subs(i, i - 1)

    Eq << Eq.induct.induct()

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=m, start=1)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
