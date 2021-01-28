from axiom.utility import prove, apply
from axiom import algebre
from sympy import *

from axiom import sets


# given: A in B
# |B - A| = |B| - |A|
@apply(imply=True)
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equality(abs(B - A), abs(B) - abs(A))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    subset = Subset(A, B, evaluate=False)

    Eq << apply(subset)

    Eq << sets.imply.equal.principle.addition.apply(B - A, B & A)

    Eq << Eq[-1] + Eq[-2]
    
    Eq << subset.intersect(A)

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)


if __name__ == '__main__':
    prove(__file__)

