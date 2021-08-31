from util import *


@apply
def apply(self):
    fx, *limits = self.of(ReducedMax[Cup[FiniteSet]])
    return Equal(self, Maxima(fx, *limits), evaluate=False)


@prove(provable=False)
def prove(Eq):
    f = Function(real=True)
    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    Eq << apply(ReducedMax({f(x): Element(x, S)}))


if __name__ == '__main__':
    run()