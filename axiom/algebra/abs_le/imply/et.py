from util import *



@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Abs)
    return LessEqual(x, a), GreaterEqual(x, -a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << algebra.abs_le.imply.le.apply(Eq[0])

    Eq << -algebra.abs_le.imply.le.apply(Eq[0], negate=True)


if __name__ == '__main__':
    run()
# created on 2018-07-30
# updated on 2018-07-30
