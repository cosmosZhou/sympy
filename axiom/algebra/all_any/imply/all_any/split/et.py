from util import *
import axiom



@apply
def apply(given, index=None):
    (fn, *limits_e), *limits_f = given.of(ForAll[Exists])
    eqs = fn.of(And)

    if index is None:
        eqs = tuple(ForAll(Exists(eq, *limits_e), *limits_f) for eq in eqs)
        return eqs

    eq = eqs[index]

    return ForAll(Exists(eq, *limits_e), *limits_f)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(ForAll[x:0:a](Exists[y:0:b]((g(x, y, z) <= 1) & (f(x, y, z) >= 1))), index=0)

    Eq << Eq[0].this.function.function.apply(algebra.et.imply.cond, index=0)


if __name__ == '__main__':
    run()

