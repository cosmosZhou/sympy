from util import *


@apply
def apply(self):
    fx, *limits = self.of(ReducedMin[Cup[FiniteSet]])
    return Equal(self, Minima(fx, *limits), evaluate=False)


@prove(provable=False)
def prove(Eq):
    f = Function(real=True)
    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(ReducedMin({f(x): Element(x, S)}))


if __name__ == '__main__':
    run()
# created on 2019-01-16
