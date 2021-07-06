from util import *


@apply
def apply(imply):
    ou, *limits = imply.of(Any[Or])

    return Or(*(Any(eq, *limits) for eq in ou))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real, given=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Any[x:A]((g(x) > 0) | (f(x) > 0)))

    Eq <<= ~Eq[0] & Eq[1]

    Eq << Eq[-1].this.args[0].apply(algebra.all_et.imply.et.all)


if __name__ == '__main__':
    run()
