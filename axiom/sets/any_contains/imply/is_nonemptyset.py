from util import *


@apply
def apply(given):
    contains, *limits = given.of(Any)
    x, B = contains.of(Contains)
    return Unequal(B, B.etype.emptySet)


@prove
def prove(Eq):
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real, given=True)
    e = Symbol.e(real=True)

    Eq << apply(Any[e:A](Contains(e, B)))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

