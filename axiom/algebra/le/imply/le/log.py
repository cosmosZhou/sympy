from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    assert lhs > 0

    return LessEqual(log(lhs), log(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(positive=True)
    y = Symbol.y(real=True)
    Eq << apply(LessEqual(x, y))

    Eq << algebra.ge.imply.ge.log.apply(Eq[0].reversed).reversed

    

    

    

    

    

    

    


if __name__ == '__main__':
    run()