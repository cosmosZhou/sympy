from util import *


@apply
def apply(self):
    coeff = 1
    args = []
    for arg in self.of(Mul):
        if arg.is_Sin:
            args.append(arg.arg)
        else:
            coeff *= arg
    x, y = args
    return Equal(self, (cos(x - y) - cos(x + y)) * coeff / 2)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x) * sin(y))

    Eq << Eq[-1].this.find(Cos[Expr - Expr]).apply(geometry.cos.to.add.principle)

    Eq << Eq[-1].this.find(Cos[Expr + Expr]).apply(geometry.cos.to.add.principle)


if __name__ == '__main__':
    run()
# created on 2020-12-03
# updated on 2020-12-03
