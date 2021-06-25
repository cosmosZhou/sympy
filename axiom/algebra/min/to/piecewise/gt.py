from util import *


@apply
def apply(self):
    arg, *args = self.of(Min)
    this = self.func(*args)
    rhs = Piecewise((arg, this > arg), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Min(x, y))

    Eq << Eq[0].this.rhs.apply(algebra.piecewise.swap.front)

    Eq << Eq[-1].lhs.this.apply(algebra.min.to.piecewise)

    z = Symbol.z(real=True)
    Eq << Eq[-1].subs(x, z)
    Eq << Eq[-1].subs(y, x)
    Eq << Eq[-1].subs(z, y)


if __name__ == '__main__':
    run()