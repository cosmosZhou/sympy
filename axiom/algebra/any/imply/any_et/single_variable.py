from util import *


@apply
def apply(given):
    function, *limits = given.of(Any)
    assert len(limits) == 1
    variable = limits[0][0]
    cond = given.limits_cond
    assert not cond
    return Any[variable]((function & cond).simplify())


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Any[e:g(e) > 0](f(e) > 0))

    S = Symbol.S(conditionset(e, g(e) > 0))

    Eq << Any[e:S](f(e) > 0, plausible=True)

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << sets.any.imply.any_et.single_variable.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.function.args[0].rhs.definition


if __name__ == '__main__':
    run()

