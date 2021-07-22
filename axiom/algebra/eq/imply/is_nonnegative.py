from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    if rhs.is_nonnegative:
        x = lhs
    elif lhs.is_nonnegative:
        x = rhs
    
    return GreaterEqual(x, 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(nonnegative=True)
    Eq << apply(Equal(a, b))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()