from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebre


# given A & B = {} => A - B = A
@apply
def apply(given, peicewise_A, peicewise_B):
    AB = axiom.is_emptyset(given)
    A, B = axiom.is_Intersection(AB)
    
    (fx, c0_A), (_fx, _) = axiom.is_Piecewise(peicewise_A)
    (gx, c0_B), (_gx, _) = axiom.is_Piecewise(peicewise_B)
    
    x, _A = axiom.is_Contains(c0_A)
    _x, _B = axiom.is_Contains(c0_B)
    
    assert x == _x
    
    if A != _A:
        A, B = B, A
        
    assert A == _A
    assert B == _B    

    return Equality(peicewise_A + peicewise_B,
                    Piecewise((fx + _gx, Contains(x, A)),
                              (_fx + gx, Contains(x, B)),
                              (_fx + _gx, True)))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    f_quote = Function("f'", nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    g_quote = Function("g'", nargs=(), shape=(), integer=True)

    Eq << apply(Equality(A & B, A.etype.emptySet),
                Piecewise((f(x), Contains(x, A)), (f_quote(x), True)),
                Piecewise((g(x), Contains(x, B)), (g_quote(x), True)))
    
    Eq << Eq[1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].bisect(Contains(x, A)).split()
    
    Eq << Eq[-2].this().function.simplify()
    
    Eq << Eq[-1].this().function.simplify()
    
    Eq << sets.is_emptyset.imply.forall_notcontains.apply(Eq[0], wrt=Eq[-1].variable)
    
    Eq << Eq[-1].apply(algebre.condition.imply.equal.piecewise, Eq[-2].lhs, invert=True)


if __name__ == '__main__':
    prove(__file__)

