from util import *


@apply
def apply(self):
    fx, * limits, limit = self.of(Cup)
    if limits:
        ecs = ((Cup(e, *limits).simplify(), c) for e, c in fx.args)
        fx = Piecewise(*ecs)

    x, s = limit.to_setlimit()

    return Equal(self, fx.as_multiple_terms(x, s, cls=Cup))


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g, F = Function(etype=dtype.real)

    Eq << apply(Cup[y:F(x), x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Cup[y:F(x)](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))).this.apply(sets.cup.to.piece)

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (x, B))

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.union.single_variable)


if __name__ == '__main__':
    run()
# created on 2018-10-03
