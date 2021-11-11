from util import *


@apply
def apply(given, piecewise, index=None):
    cond, q = given.of(Infer)
    old, new = q.of(Equal)
    [*ecs] = piecewise.of(Piecewise)
    if index is None:
        hit = False
        for index, (e, c) in enumerate(ecs):
            # c >> cond
            if (cond | c.invert()).simplify():
                e = e._subs(old, new)
                ecs[index] = (e, c)
                hit = True
        assert hit
    else:
        e, c = ecs[index]
        assert c == cond or c.is_And and cond in c._argset
        e = e._subs(old, new)
        ecs[index] = (e, c)

    return Equal(piecewise, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Infer(Element(x, A), Equal(f(x), 1)), Piecewise((f(x), Element(x, A) & Element(x, B)), (-1, True)))

    Eq << Eq[1] - Eq[1].rhs

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.piece.st.two_pieces)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piece.st.two_pieces)

    Eq << algebra.eq.given.ou.apply(Eq[-1])

    Eq << algebra.ou.given.infer.apply(Eq[-1], 1)

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(sets.el.imply.el.split.intersect)


if __name__ == '__main__':
    run()
# created on 2018-07-23
# updated on 2018-07-23
