from util import *


@apply
def apply(ceil):
    m = ceil.of(Ceiling)
    args = m.of(Max)
    args = [ceiling(arg) for arg in args]

    return Equal(ceil, Max(*args))


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    Eq << apply(ceiling(Max(x, y)))

    Eq << Eq[0].apply(algebra.eq_ceiling.given.et)

    Eq <<= algebra.imply.gt.ceiling.apply(x), algebra.imply.gt.ceiling.apply(y)

    Eq << algebra.gt.gt.imply.gt.max.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.add)

    Eq << Eq[-1] + 1


if __name__ == '__main__':
    run()
