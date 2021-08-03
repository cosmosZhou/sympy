from util import *


@apply(simplify=False)
def apply(given, x):
    lhs, rhs = given.of(LessEqual)
    return LessEqual(lhs + x, rhs + x, evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    z = Symbol.z(real=True, given=True)
    Eq << apply(x <= y, z)

    Eq << Eq[0] + z


if __name__ == '__main__':
    run()