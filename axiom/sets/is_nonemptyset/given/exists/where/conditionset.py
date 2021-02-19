from sympy.core.relational import Unequality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Exists
from sympy import Symbol
from axiom import sets
import axiom
from sympy.sets.conditionset import conditionset
from sympy.sets.sets import Interval
from sympy.core.function import Function
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
    
    Eq << apply(Unequality(conditionset(x, f(x) > 1, S), x.emptySet))
    
    A = Symbol.A(definition=Eq[0].lhs)
    
    Eq << A.this.definition
    
    Eq << Exists[x:S](Contains(x, A), plausible=True)
    
    Eq << Eq[-1].this.function.subs(Eq[2])
    
    Eq << Eq[-1].simplify()

    Eq << Eq[-1].subs(Eq[2])


if __name__ == '__main__':
    prove(__file__)

