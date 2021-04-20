from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


@apply
def apply(A, B):
    return GreaterEqual(abs(Union(A, B)), abs(A))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(A, B)

    Eq << Eq[-1].lhs.arg.this.rewrite(complement=0)
    
    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)

    Eq << Eq[-1] + GreaterEqual(Eq[-1].rhs.args[1], 0, plausible=True)
    
    Eq << Eq[-1].this.apply(algebra.ge.simplify.common_terms)


if __name__ == '__main__':
    prove()

