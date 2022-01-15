from util import *


@apply
def apply(self):
    fx, * limits, limit = self.of(Cap)
    if limits:
        ecs = ((Cap(e, *limits).simplify(), c) for e, c in fx.args)
        fx = Piecewise(*ecs)

    return Equal(self, fx.as_multiple_terms(*limit.to_setlimit(), cls=Cap))


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g, F = Function(etype=dtype.real)

    Eq << apply(Cap[y:F(x), x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Cap[y:F(x)](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))).this.apply(sets.cap.to.piece)

    Eq << sets.eq.imply.eq.cap.apply(Eq[-1], (x, B))

    Eq << Eq[-1].this.rhs.apply(sets.cap.to.intersect.single_variable)


if __name__ == '__main__':
    run()

# created on 2021-01-26
