from util import *


@apply
def apply(self):
    x, y = self.of(ReducedSum[Mul])
    
    assert len(x.shape) == len(y.shape) == 1
    rhs = x @ y
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    y = Symbol.y(shape=(n,), real=True)
    x = Symbol.x(shape=(n,), real=True)
    Eq << apply(ReducedSum(x * y))

    Eq << Eq[0].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()