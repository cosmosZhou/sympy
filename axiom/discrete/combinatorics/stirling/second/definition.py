from util import *


@apply
def apply(n, k):
    from sympy.functions.combinatorial.numbers import Stirling
    i = n.generate_var(k.free_symbols, integer=True)
    return Equal(Stirling(n, k), Sum[i:0:k + 1]((-1) ** (k - i) * binomial(k, i) * i ** n) / factorial(k))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    from sympy.functions.combinatorial.numbers import Stirling
    k = Symbol.k(integer=True, nonnegative=True, given=False)
    n = Symbol.n(integer=True, nonnegative=True)
    Eq.hypothesis = apply(n, k)

    i = Eq.hypothesis.rhs.args[1].variable

    Eq << discrete.combinatorics.stirling.second.recurrence.apply(n, k)

    Eq << Eq[-1].subs(Eq.hypothesis)

    y = Symbol.y(Lamda[n](Stirling(n, k + 1)))

    Eq << y.equality_defined()

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    Eq << Eq[-1].this.apply(algebra.eq.rsolve.linear, y[n])

    Eq << discrete.combinatorics.binomial.fraction.apply(k + 1, i).reversed * (k + 1 - i)

    Eq << Eq[-2].subs(Eq[-1])

    Eq.stirling_solution = Eq[-1].subs(Eq[2])

    Eq << Eq.stirling_solution.subs(n, k + 1)

    Eq << Eq[-1].this.function / (k + 1) ** (k + 1)

    Eq << Eq.stirling_solution.this.function / (k + 1) ** n

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.sub)

    Eq << Eq[-1] * (k + 1) ** n

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq.ratsimp = Eq[-1].this.rhs.args[0].ratsimp()

    Eq.powsimp = Eq[-1].rhs.args[1].args[-1].this.function.powsimp()

    Eq << discrete.combinatorics.permutation.factorial.sum.apply(k + 1)

    Eq << Eq[-1] * (-1) ** (k + 1)

    Eq << Eq[-1].this.rhs.astype(Sum)

    Eq << Eq[-1].this.rhs.split(Slice[-1:]).reversed

    Eq << Eq[-1].subs(Eq.powsimp.reversed)

    Eq << Eq[-1] - Eq[-1].lhs.args[0]

    Eq << Eq.ratsimp.subs(Eq[-1])

    Eq << Eq[-1] - Eq[-1].lhs.args[0] - Eq[-1].rhs.args[0]

    Eq << Eq[-1] * factorial(k + 1)

    Eq << Eq[-1].this.lhs.expand()

    Eq.k_factorial_expand = discrete.factorial.to.mul.apply(Factorial(k + 1)).this.rhs.expand()

    Eq << Eq[-1].this.lhs.args[1].subs(Eq.k_factorial_expand)

    Eq << Eq[-1].this.rhs.subs(Eq.k_factorial_expand)

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-1].this.lhs.astype(Sum)

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    Eq << Eq.induct * factorial(k + 1)

    Eq << Eq[-1].this.rhs.split(Slice[-1:])

    Eq << -Eq[-1].reversed + Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.lhs.astype(Sum)

    Eq << Eq.induct.induct()

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=k)


if __name__ == '__main__':
    run()
