from util import *


@apply
def apply(piecewise):
    ec0, ec1, *ec = piecewise.args

    e0, c0 = ec0
    e1, c1 = ec1
    if not ec:
        return Equal(piecewise, Piecewise((e1, c0.invert()), (e0, True)))

    return Equal(piecewise, Piecewise((e1, c1 & c0.invert()), (e0, c0), *ec))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B = Symbol(etype=dtype.real * k)
    f, g, h = Function(shape=(), real=True)

    Eq << apply(Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True)))

    p = Symbol(Eq[0].lhs)
    q = Symbol(Eq[0].rhs)
    Eq << p.this.definition

    Eq << q.this.definition

    Eq << algebra.eq_piece.imply.ou.apply(Eq[-1])

    Eq << algebra.ou.imply.eq.piece.apply(Eq[-1], wrt=q)

    Eq << Eq[-1].subs(Eq[1].reversed).reversed

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

