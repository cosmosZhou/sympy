from sympy.core.relational import GreaterThan
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.sets import Union
from sympy import Symbol
from axiom import algebre


@apply(imply=True)
def apply(A, B):
    return GreaterThan(abs(Union(A, B)), abs(A))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(A, B)

    Eq << Eq[-1].lhs.arg.this.rewrite(complement=0)
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)

    Eq << Eq[-1].subs(Eq[-1].rhs.args[1], 0)


if __name__ == '__main__':
    prove(__file__)

