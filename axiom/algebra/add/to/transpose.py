from util import *


@apply
def apply(self, evaluate=False):
    args = self.of(Add)
    rhs = Transpose(Add(*(arg.of(Transpose) for arg in args)).simplify(), evaluate=evaluate)
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    A, B = Symbol(real=True, shape=(m, n))
    Eq << apply(A.T + B.T)
    i, j = Symbol(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()
