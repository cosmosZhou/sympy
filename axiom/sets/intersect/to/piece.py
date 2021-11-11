from util import *




@apply
def apply(self):
    [*args] = self.of(Intersection)
    for i, piecewise in enumerate(args):
        if piecewise.is_Piecewise:
            del args[i]
            s = Intersection(*args)

            ecs = ((e & s, c) for e, c in piecewise.args)
            return Equal(self, Piecewise(*ecs))

@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    f, g, h = Function(etype=dtype.real)

    Eq << apply(Intersection(Piecewise((f(x), x > 0), (g(x), True)), h(x), evaluate=False))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=1)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=1, invert=True)

if __name__ == '__main__':
    run()

# created on 2018-09-25
# updated on 2018-09-25
