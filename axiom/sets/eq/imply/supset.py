from util import *


@apply
def apply(given):
    assert given.is_Equal
    A, B = given.args
    assert A.is_set and B.is_set
    return Supset(A, B)


@prove
def prove(Eq):
    A, B = Symbol(etype=dtype.integer, given=True)

    equality = Equal(A, B)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    run()

