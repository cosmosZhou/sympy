from util import *


@apply(simplify=False)
def apply(self, factor):
    num, den = self.of(Expr / Expr)
    factor = sympify(factor)
    assert factor.is_nonzero

    return Equal(self, (num * factor).expand() / (den * factor).expand(), evaluate=False)


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    c, d = Symbol(real=True, zero=False)

    Eq << apply((a + 1 / c) / (b + 1 / d), c * d)

    Eq << (c * d * (b + 1 / d)).this.expand()

    Eq << (c * d * (a + 1 / c)).this.expand()

    Eq << Eq[0].subs(Eq[-2].reversed, Eq[-1].reversed)

if __name__ == '__main__':
    run()
# created on 2020-06-29
