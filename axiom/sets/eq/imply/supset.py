
from util import *


# given: A = B
# A >> B
@apply
def apply(given):
    assert given.is_Equal
    A, B = given.args
    assert A.is_set and B.is_set
    return Supset(A, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    equality = Equal(A, B)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    run()

