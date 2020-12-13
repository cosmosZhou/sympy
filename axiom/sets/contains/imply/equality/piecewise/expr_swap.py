from axiom.utility import plausible
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
import axiom
from sympy.core.symbol import dtype
from axiom import sets, algebre


# given: A in B 
# => A | B = B
@plausible
def apply(given, piecewise):
    assert given.is_Contains
    x, S = given.args
    
    ec = axiom.is_Piecewise(piecewise)
    _x, s = axiom.is_Contains(ec[0].cond)
    assert s in S
    assert x == _x
    f = ec[0].expr
    
    g = ec[1].expr
    
    return Equality(piecewise, Piecewise((g, Contains(x, S - s)), (f, True)).simplify())


from axiom.utility import check


def bool(cond):
    return Piecewise((1, cond), (0, True))


bool = Function.bool(nargs=(), shape=(), integer=True, eval=bool)


@check
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    S = Symbol.S(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    s = Symbol.s(definition=A & S)
    
    f = Function.f(nargs=(1,), shape=())
    g = Function.g(nargs=(1,), shape=())
    Eq << apply(Contains(x, S), Piecewise((f(x), Contains(x, s)), (g(x), True)))
    
    Eq << algebre.imply.equality.piecewise.apply(Eq[2].lhs)

    (gx, cond_contains), (fx, _) = Eq[-1].rhs.args
    p = Symbol.p(definition=Piecewise((gx, Equality(bool(cond_contains), 1)), (fx, _)))

    (gx, cond_notcontains), (fx, _) = Eq[2].rhs.args
    q = Symbol.q(definition=Piecewise((gx, Equality(bool(cond_notcontains), 1)), (fx, _)))
    
    Eq << p.this.definition
    
    Eq.p_definition = Eq[-1].this.rhs.args[0].cond.lhs.definition
    
    Eq << Eq[2].subs(Eq.p_definition.reversed)
    
    Eq.q_definition = q.this.definition
    
    Eq << Eq.q_definition.this.rhs.args[0].cond.lhs.definition

    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq.bool_equality = Equality(bool(cond_contains), bool(cond_notcontains), plausible=True)
    
    Eq << Eq.bool_equality.this.rhs.definition    
    
    Eq.forall_not_s, Eq.forall_s = Eq[-1].bisect(cond_contains).split()
    
    Eq << ~Eq.forall_not_s
    
    Eq << Eq[-1].apply(sets.notcontains.inequality.imply.et)
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq << ~Eq.forall_s
    
    Eq << Eq[-1].apply(sets.contains.inequality.imply.et, invert=True)
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << Eq.q_definition.subs(Eq.bool_equality.reversed)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].args[0].cond.rhs.definition
    
    Eq << Eq[-1].this.rhs.args[0].astype(Piecewise)
    
    Eq << Eq.p_definition.subs(Eq[-1].reversed)


    
if __name__ == '__main__':
    prove(__file__)

