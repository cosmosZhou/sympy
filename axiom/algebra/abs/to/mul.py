from util import *


@apply
def apply(self):
    args = self.of(Abs[Mul])
    return Equal(self, Mul(*(abs(arg) for arg in args)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(abs(x * y))

    Eq << Eq[0].this.rhs.apply(algebra.mul.to.abs)


if __name__ == '__main__':
    run()
