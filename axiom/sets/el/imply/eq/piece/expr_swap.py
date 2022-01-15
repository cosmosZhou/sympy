from util import *


@apply
def apply(given, piecewise):
    assert given.is_Element
    x, S = given.args

    ec = piecewise.of(Piecewise)
    _x, s = ec[0].cond.of(Element)
    assert s in S
    assert x == _x
    f = ec[0].expr

    g = ec[1].expr

    return Equal(piecewise, Piecewise((g, Element(x, S - s)), (f, True)).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(integer=True, given=True)
    S, A = Symbol(etype=dtype.integer, given=True)
    s = Symbol(A & S)
    f, g = Function(shape=())
    Eq << apply(Element(x, S), Piecewise((f(x), Element(x, s)), (g(x), True)))

    Eq << algebra.piece.swap.apply(Eq[2].lhs)

    (gx, cond_contains), (fx, _) = Eq[-1].rhs.args
    p = Symbol(Piecewise((gx, Equal(Bool(cond_contains), 1)), (fx, _)))
    (gx, cond_notcontains), (fx, _) = Eq[2].rhs.args
    q = Symbol(Piecewise((gx, Equal(Bool(cond_notcontains), 1)), (fx, _)))
    Eq << p.this.definition

    Eq.p_definition = Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[2].subs(Eq.p_definition.reversed)

    Eq.q_definition = q.this.definition

    Eq << Eq.q_definition.this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.bool_equality = Equal(Bool(cond_contains), Bool(cond_notcontains), plausible=True)

    Eq << Eq.bool_equality.this.rhs.apply(algebra.bool.to.piece)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=cond_contains)

    Eq.all_not_s, Eq.all_s = algebra.et.given.et.apply(Eq[-1])

    Eq << ~Eq.all_not_s

    Eq << Eq[-1].this.apply(algebra.cond.cond.imply.cond.subs, ret=0)

    Eq << Eq[-1].this.args[0].simplify()

    Eq <<= Eq[-1] & Eq[0]

    Eq << ~Eq.all_s

    Eq << Eq[-1].this.apply(algebra.cond.cond.imply.cond.subs, invert=True, ret=0)

    Eq << Eq[-1].this.args[0].simplify()

    Eq << Eq.q_definition.subs(Eq.bool_equality.reversed)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq_bool.to.cond)

    Eq << Eq.p_definition.subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()

# created on 2020-10-27
