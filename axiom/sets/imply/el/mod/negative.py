from util import *


@apply
def apply(self):
    n, d = self.of(Mod)
    assert n.is_integer
    assert d.is_integer
    assert d < 0
    return Element(self, Range(d + 1, 1))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True)
    d = Symbol(integer=True, negative=True)
    Eq << apply(n % d)

    Eq << Eq[0].this.lhs.apply(algebra.mod.to.add)

    Eq << sets.el_range.given.et.apply(Eq[-1], right_open=False)

    Eq << algebra.ge.given.gt.apply(Eq[-2])

    Eq <<= Eq[-2] - n, Eq[-1] - n

    Eq <<= -Eq[-2], -Eq[-1]

    Eq <<= Eq[-2] / d, Eq[-1] / d

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << algebra.imply.gt.floor.apply(n / d)


if __name__ == '__main__':
    run()

# created on 2021-04-22
