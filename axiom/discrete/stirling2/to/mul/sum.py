from util import *


from sympy.functions.combinatorial.numbers import Stirling
@apply
def apply(self):
    n, k = self.of(Stirling)
    i = n.generate_var(k.free_symbols, integer=True)
    return Equal(self, Sum[i:0:k + 1]((-1) ** (k - i) * binomial(k, i) * i ** n) / factorial(k))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True, nonnegative=True, given=False)
    n = Symbol(integer=True, nonnegative=True)
    Eq.hypothesis = apply(Stirling(n, k))

    i = Eq.hypothesis.rhs.args[1].variable
    Eq << discrete.stirling2.to.add.recurrence.apply(n, k)

    Eq << Eq[-1].subs(Eq.hypothesis)

    y = Symbol(Lamda[n](Stirling(n, k + 1)))
    Eq << y[n].this.definition

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    Eq << Eq[-1].this.apply(algebra.eq.rsolve.linear, y[n])

    Eq << discrete.mul.binom.fraction.apply(k + 1, i).reversed * (k + 1 - i)

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq[-2])

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[2], Eq[-1])

    Eq.stirling_solution = Eq[-1].this.find(Sum).expr.ratsimp()

    Eq << Eq.stirling_solution.this.expr.apply(algebra.cond.imply.cond.subs, n, k + 1, ret=0)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.cancel, wrt=Eq.stirling_solution.variable)

    Eq << Eq[-1].this.rhs.find(Sum).expr.powsimp()

    Eq << Eq[-1] * (k + 1) ** n

    Eq.factor2mul = discrete.factorial.to.mul.apply(factorial(k + 1)).this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].subs(Eq.factor2mul.reversed)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq.ratsimp = Eq[-1].this.rhs.args[0].ratsimp()

    Eq << discrete.factorial.to.sum.apply(k + 1)

    Eq << Eq[-1] * (-1) ** (k + 1)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={0, k + 1}).reversed

    Eq << Eq[-1] - Eq[-1].lhs.args[0]

    Eq << Eq.ratsimp.subs(Eq[-1])

    Eq << Eq[-1] - Eq[-1].lhs.args[0] - Eq[-1].rhs.args[0]

    Eq << Eq[-1] * factorial(k + 1)

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    Eq << Eq.induct * factorial(k + 1)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.pop_back)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=k)

    


if __name__ == '__main__':
    run()
# created on 2020-10-13
# updated on 2022-01-18
