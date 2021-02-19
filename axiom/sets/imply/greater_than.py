from sympy import *
from axiom.utility import prove, apply
from axiom import algebre


@apply
def apply(A, B):
    return GreaterThan(abs(Union(A, B)), abs(A))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(A, B)

    Eq << Eq[-1].lhs.arg.this.rewrite(complement=0)
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)

    Eq << Eq[-1] + GreaterThan(Eq[-1].rhs.args[1], 0, plausible=True)


if __name__ == '__main__':
    prove(__file__)

