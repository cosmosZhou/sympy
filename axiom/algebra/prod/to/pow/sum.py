from util import *


@apply
def apply(self, simplify=True):
    (b, e), *limits = self.of(Product[Pow])
    assert not b.has(*self.variables)
    return Equal(self, b ** Sum(e, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Function(real=True)
    a = Symbol(real=True)
    Eq << apply(Product[i:n](a ** f(i)))

    Eq << Eq[0].subs(n, 0)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq[0] * a ** f(n)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.prod.limits.push_back)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.find(Add[Sum]).apply(algebra.add.to.sum.limits.push_back)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n)

    


if __name__ == '__main__':
    run()
# created on 2022-01-15
