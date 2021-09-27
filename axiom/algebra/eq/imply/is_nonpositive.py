from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    if rhs.is_nonpositive:
        x = lhs
    elif lhs.is_nonpositive:
        x = rhs

    return LessEqual(x, 0)


@prove
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(nonpositive=True)
    Eq << apply(Equal(a, b))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
