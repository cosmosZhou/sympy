from util import *


@apply
def apply(self):
    [*args] = self.of(Add)
    for i, p in enumerate(args):
        if p.is_Piecewise:
            break
    else:
        return

    del args[i]
    a = Add(*args)
    return Equal(self, Piecewise(*((e + a, c) for e, c in p.args)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    f, g, h = Function(real=True)
    Eq << apply(Piecewise((f(x), Element(x, A)), (g(x), True)) + h(x))

    Eq << Eq[0].this.rhs.apply(algebra.piece.to.add, -h(x))


if __name__ == '__main__':
    run()


