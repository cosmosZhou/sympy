from util import *


@apply
def apply(self):
    coeff = 1
    for arg in self.of(Mul):
        if arg.is_Sin:
            x = arg.arg
        elif arg.is_Cos:
            y = arg.arg
        else:
            coeff *= arg
            
    return Equal(self, (sin(x + y) + sin(x - y)) * coeff / 2)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(sin(x) * cos(y))

    Eq << Eq[-1].this.find(Sin[Expr - Expr]).apply(geometry.sin.to.add.principle)

    Eq << Eq[-1].this.find(Sin[Expr + Expr]).apply(geometry.sin.to.add.principle)


if __name__ == '__main__':
    run()
# created on 2020-12-02
# updated on 2020-12-02
