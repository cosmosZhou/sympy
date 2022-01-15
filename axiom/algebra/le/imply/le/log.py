from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    assert lhs > 0

    return LessEqual(log(lhs), log(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(positive=True)
    y = Symbol(real=True)
    Eq << apply(LessEqual(x, y))

    Eq << algebra.ge.imply.ge.log.apply(Eq[0].reversed).reversed
















if __name__ == '__main__':
    run()
# created on 2019-08-23
