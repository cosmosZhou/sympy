from util import *



@apply
def apply(self):
    n, factorial_n_1 = self.of(Mul)
    n_1 = factorial_n_1.of(Factorial)

    assert n_1 == n - 1
    assert n > 0

    return Equal(self, factorial(n))


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol(integer=True, positive=True)
    Eq << apply(n * factorial(n - 1))

    Eq << Eq[0].this.rhs.apply(discrete.factorial.to.mul)


if __name__ == '__main__':
    run()
# created on 2020-08-07
