from util import *
import axiom



@apply
def apply(self):
    flr, d = self.of(Mul)
    if d.is_Floor:
        flr, d = d, flr
    div_x_d = flr.of(Floor)
    x, _d = axiom.is_Divide(div_x_d)
    assert d == _d

    assert d.is_integer and x.is_integer
    return Equal(self, x - x % d)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(x // d * d)

    Eq << algebra.mod.to.add.apply(x % d)

    Eq << Eq[0] - Eq[1]


if __name__ == '__main__':
    run()
