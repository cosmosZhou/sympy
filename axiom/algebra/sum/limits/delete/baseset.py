from util import *


@apply
def apply(self):
    function, (x, cond, space) = self.of(Sum)
    cond &= Contains(x, space)
    return Equal(self, Sum[x:cond](function))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.integer*n)

    x = Symbol.x(integer=True, shape=(oo,))
    f = Function.f(real=True, shape=())
    g = Function.g(real=True, shape=())
    Eq << apply(Sum[x[:n]:g(x[:n]) > 0:A](f(x[:n])))

    Eq << Eq[0].this.lhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

if __name__ == '__main__':
    run()

