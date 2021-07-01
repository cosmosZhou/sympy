from util import *


@apply
def apply(self):
    [*args] = self.of(Union)
    for i, piecewise in enumerate(args):
        if piecewise.is_Piecewise:
            del args[i]
            s = Union(*args)

            ecs = ((e | s, c) for e, c in piecewise.args)
            return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)
    h = Function.h(etype=dtype.real)
    t = Function.t(etype=dtype.real)

    Eq << apply(Union(Piecewise((f(x), x > 0), (g(x), True)), h(x), t(x), evaluate=False))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=1)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=1, invert=True)


if __name__ == '__main__':
    run()

