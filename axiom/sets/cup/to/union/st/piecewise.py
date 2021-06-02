from util import *


import axiom


@apply
def apply(self):
    fx, *limits = self.of(Cup)
    * limits, limit = limits
    if limits:
        ecs = ((Cup(e, *limits).simplify(), c) for e, c in fx.args)
        fx = Piecewise(*ecs)

    return Equal(self, fx.as_multiple_terms(*axiom.limit_is_set((limit,)), cls=Cup))


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

    Eq << apply(Cup[y:F(x), x:B](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))))

    Eq << Cup[y:F(x)](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))).this.apply(sets.cup.to.piecewise)

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (x, B))

    Eq << Eq[-1].this.rhs.apply(sets.cup.to.union.single_variable)

if __name__ == '__main__':
    run()
