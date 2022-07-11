from util import *


@apply
def apply(is_zero, n=None):
    x = is_zero.of(Equal[Cos, 0])
    return Equal(x, S.Pi / 2 + S.Pi * Floor(x / S.Pi))


@prove
def prove(Eq):
    from axiom import sets, geometry, algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0))

    Eq << sets.imply.el.floor.apply(x, S.Pi)

    Eq << geometry.cos_is_zero.imply.cos_is_zero.apply(Eq[0], -Floor(x / S.Pi))

    Eq << geometry.cos_is_zero.el.imply.eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.apply(algebra.eq.transport)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-24
