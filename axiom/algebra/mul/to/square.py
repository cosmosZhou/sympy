from util import *


@apply
def apply(self, evaluate=False):
    args = []

    for arg in self.of(Mul):
        if arg.is_Number:
            assert arg >= 0
            args.append(sqrt(arg))
        else:
            arg = arg.of(Basic ** 2)
            args.append(arg)

    return Equal(self, Mul(*args) ** 2, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(4 * (x + y) ** 2)

    Eq << Eq[-1].this.find(Pow).apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(Pow).apply(algebra.square.to.add)


if __name__ == '__main__':
    run()

