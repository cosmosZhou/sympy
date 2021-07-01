from util import *


@apply
def apply(self, evaluate=False):
    args = self.of(Add)
    rhs = Transpose(Add(*(arg.of(Transpose) for arg in args)).simplify(), evaluate=evaluate)
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    A = Symbol.A(real=True, shape=(m, n))
    B = Symbol.B(real=True, shape=(m, n))
    Eq << apply(A.T + B.T)
    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    run()