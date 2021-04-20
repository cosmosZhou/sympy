from sympy import *
from axiom.utility import prove, apply
from axiom import sets
import axiom
# given: A != {}
# Exists[x] (x in A)


@apply
def apply(imply):
    s = axiom.is_nonemptyset(imply)
    x, cond, baseset = axiom.is_ConditionSet(s)
    return Exists[x:baseset](cond)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.complex)
    x = Symbol.x(complex=True)
    f = Function.f(real=True)
    
    Eq << apply(Unequal(conditionset(x, f(x) > 1, S), x.emptySet))
    
    A = Symbol.A(Eq[0].lhs)
    
    Eq << A.this.definition
    
    Eq << Exists[x:S](Contains(x, A), plausible=True)
    
    Eq << Eq[-1].this.function.subs(Eq[2])
    
    Eq << Eq[-1].simplify()

    Eq << Eq[-1].subs(Eq[2])


if __name__ == '__main__':
    prove()

