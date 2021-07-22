from util import *


@apply
def apply(self):
    (piecewise, gx), limit = self.of(Cup[Intersection[Piecewise, Basic]])    
    ecs = ((e & gx, c) for e, c in piecewise)
    
    return Equal(self, Piecewise(*ecs).as_multiple_terms(*limit.to_setlimit(), Cup))


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)

    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    h = Function.h(etype=dtype.real)
    g = Function.g(etype=dtype.real)

    Eq << apply(Cup[x:A](Intersection(Piecewise((f(x), Contains(x, C)), (h(x), True)), g(x), evaluate=False)))

    Eq << Eq[0].this.lhs.expr.apply(sets.intersection.to.piecewise)

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.union.st.piecewise)


if __name__ == '__main__':
    run()

