
from util import *


# given: A ⊃ B
# |A| >= |B|
@apply
def apply(given):
    assert given.is_Supset
    A, B = given.args

    return GreaterEqual(abs(A), abs(B))




@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Supset(A, B))

    Eq << Eq[0].reversed

    Eq << sets.subset.imply.le.apply(Eq[-1])

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

