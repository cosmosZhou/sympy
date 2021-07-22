from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    if rhs.is_negative:
        x = lhs
    elif lhs.is_negative:
        x = rhs
    
    return Less(x, 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(negative=True)
    Eq << apply(Equal(a, b))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()