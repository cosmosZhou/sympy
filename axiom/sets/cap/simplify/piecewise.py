from util import *


import axiom


@apply
def apply(self):
    intersection, *limits = self.of(Cap)
    x, S = axiom.limit_is_set(limits)
    piecewise, gx = intersection.of(Union)
    if not piecewise.is_Piecewise:
        piecewise, gx = gx, piecewise

    ecs = ((e | gx, c) for e, c in piecewise.of(Piecewise))

    return Equal(self, Piecewise(*ecs).as_multiple_terms(x, S, Cap))


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)

    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    h = Function.h(etype=dtype.real)
    g = Function.g(etype=dtype.real)

    Eq << apply(Cap[x:A](Union(Piecewise((f(x), Contains(x, C)), (h(x), True)), g(x), evaluate=False)))

    Eq << Eq[0].this.lhs.function.apply(sets.union.to.piecewise)

    Eq << Eq[-1].this.lhs.apply(sets.cap.to.intersection.st.piecewise)


if __name__ == '__main__':
    run()

