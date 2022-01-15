from util import *



@apply
def apply(imply):
    function, *limits = imply.of(Any)

    variables = tuple(v for v, *_ in limits)
    return Any[variables]((function & imply.limits_cond).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)
    f, g, h = Function(shape=(), integer=True)
    Eq << apply(Any[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=0)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
# created on 2018-03-25
