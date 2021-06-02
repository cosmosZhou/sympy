from util import *


@apply
def apply(self, *, simplify=True):
    piecewise = []
    delta = []
    for arg in self.of(Mul):
        if arg.is_Piecewise:
            piecewise.append(arg)
        else:
            delta.append(arg)

    if not piecewise:
        return

    delta = self.func(*delta, evaluate=False)
    if len(piecewise) == 1:
        result, *_ = piecewise
        if not delta.is_One:
            result = result.func(*((e * delta, c) for e, c in result.args))
    else:
        result = piecewise[0]
        for i in range(1, len(piecewise)):
            result = result.mul(piecewise[i])

        if not delta.is_One:
            result = result.func(*((e * delta, c) for e, c in result.args))
    if simplify:
        result = result.simplify()
    return Equal(self, result, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)
    Eq << apply(Piecewise((g(x), x > 0), (h(x), True)) * y)

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0)

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0, invert=True)


if __name__ == '__main__':
    run()
