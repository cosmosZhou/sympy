from util import *


@apply
def apply(imply):
    x, (_x, cond, *baseset) = imply.of(Unequal[Cup[FiniteSet], EmptySet])
    assert _x == x
    if baseset:
        [baseset] = baseset
        return Any[x:baseset](cond)
    else:
        return Any[x](cond)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.complex)
    x = Symbol.x(complex=True)
    f = Function.f(real=True)
    
    Eq << apply(Unequal(conditionset(x, f(x) > 1, S), x.emptySet))
    
    A = Symbol.A(Eq[0].lhs)
    
    Eq << A.this.definition
    
    Eq << Any[x:S](Contains(x, A), plausible=True)
    
    Eq << Eq[-1].this.function.subs(Eq[2])
    
    Eq << Eq[-1].simplify()

    Eq << Eq[-1].subs(Eq[2])


if __name__ == '__main__':
    run()

