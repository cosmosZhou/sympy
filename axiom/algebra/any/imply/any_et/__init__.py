from util import *


@apply
def apply(given):
    function, *limits = given.of(Any)
    return Any[given.variables]((function & given.limits_cond).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)
    Eq << apply(Any[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))

    A = Symbol.A(conditionset(x, f(x) > 0))
    B = Symbol.B(conditionset(y, g(y) > 0))

    Eq << Any[x:A, y:B](h(x, y) > 0, plausible=True)
    Eq << Eq[-1].this.limits[0][1].definition
    Eq << Eq[-1].this.limits[1][1].definition

    Eq << sets.any.imply.any_et.apply(Eq[-2], simplify=False)
    Eq << Bool(Eq[-1].function).this.arg.args[1].rhs.definition
    Eq << Eq[-1].this.rhs.arg.args[2].rhs.definition

    Eq << algebra.eq.imply.equivalent.apply(Eq[-1])

    Eq << algebra.equivalent.cond.imply.cond.apply(Eq[-1], Eq[-4])


if __name__ == '__main__':
    run()

from . import single_variable
