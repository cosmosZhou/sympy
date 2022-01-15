from util import *


@apply
def apply(self):
    ecs = []
    for e, c in self.of(ReducedArgMin[Piecewise]):
        ecs.append((ReducedArgMin(e), c))

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra

    m = Symbol(integer=True, positive=True)
    f, g = Function(real=True, shape=(m,))
    x, a, b = Symbol(real=True)
    Eq << apply(ReducedArgMin(Piecewise((f(x), a > b), (g(x), True))))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool)
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, invert=True)





if __name__ == '__main__':
    run()
# created on 2021-12-17
