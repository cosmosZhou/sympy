from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


# given: A in B 
# => A | B = B
@apply
def apply(given, piecewise):
    assert given.is_Contains
    x, S = given.args
    
    ec = axiom.is_Piecewise(piecewise)
    _x, s = axiom.is_Contains(ec[0].cond)
    assert s in S
    assert x == _x
    f = ec[0].expr
    
    g = ec[1].expr
    
    return Equality(piecewise, Piecewise((g, Contains(x, S // s)), (f, True)).simplify())

@prove
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    S = Symbol.S(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    s = Symbol.s(A & S)
    
    f = Function.f(nargs=(1,), shape=())
    g = Function.g(nargs=(1,), shape=())
    Eq << apply(Contains(x, S), Piecewise((f(x), Contains(x, s)), (g(x), True)))
    
    Eq << algebre.piecewise.swap.front.apply(Eq[2].lhs)

    (gx, cond_contains), (fx, _) = Eq[-1].rhs.args
    p = Symbol.p(Piecewise((gx, Equality(Boole(cond_contains), 1)), (fx, _)))

    (gx, cond_notcontains), (fx, _) = Eq[2].rhs.args
    q = Symbol.q(Piecewise((gx, Equality(Boole(cond_notcontains), 1)), (fx, _)))
    
    Eq << p.this.definition
    
    Eq.p_definition = Eq[-1].this.rhs.args[0].cond.lhs.astype(Piecewise)
    
    Eq << Eq[2].subs(Eq.p_definition.reversed)
    
    Eq.q_definition = q.this.definition
    
    Eq << Eq.q_definition.this.rhs.args[0].cond.lhs.astype(Piecewise)

    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq.bool_equality = Equality(Boole(cond_contains), Boole(cond_notcontains), plausible=True)
    
    Eq << Eq.bool_equality.this.rhs.astype(Piecewise)    
    
    Eq << Eq[-1].bisect(cond_contains)
    
    Eq.forall_not_s, Eq.forall_s = algebre.et.given.cond.apply(Eq[-1])
    
    Eq << ~Eq.forall_not_s
    
    Eq << Eq[-1].apply(algebre.cond.cond.imply.et)
    
    Eq << Eq[-1].this.args[0].simplify()
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq << ~Eq.forall_s
    
    Eq << Eq[-1].apply(algebre.cond.cond.imply.et, invert=True)
    
    Eq << Eq[-1].this.args[0].simplify()
    
    Eq << Eq.q_definition.subs(Eq.bool_equality.reversed)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].args[0].cond.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[0].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq.p_definition.subs(Eq[-1].reversed)


    
if __name__ == '__main__':
    prove(__file__)

