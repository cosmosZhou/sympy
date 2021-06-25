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
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)
    F = Function.F(etype=dtype.real)

    Eq << apply(Cap[y:F(x), x:B](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))))

    Eq << Cap[y:F(x)](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))).this.apply(sets.cap.to.piecewise)

    Eq << sets.eq.imply.eq.cap.apply(Eq[-1], (x, B))

    Eq << Eq[-1].this.rhs.apply(sets.cap.to.intersection.single_variable)


if __name__ == '__main__':
    run()

