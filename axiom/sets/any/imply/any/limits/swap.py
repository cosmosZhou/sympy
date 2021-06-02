from util import *



@apply
def apply(given):
    assert given.is_Exists
    limits = [(x,) for x, *_ in given.limits]
    limits[0] = (limits[0][0], given.function)
    return Exists(given.limits_cond, *limits)


@prove
def prove(Eq):
    from axiom import sets
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Exists[e:g(e) > 0](f(e) > 0))

    A = Symbol.A(conditionset(e, g(e) > 0))
    B = Symbol.B(conditionset(e, f(e) > 0))

    Eq.A_definition = A.this.definition
    Eq.B_definition = B.this.definition

    Eq << Exists[e:A](Contains(e, B), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << Eq[-1].subs(Eq.A_definition)

    Eq << sets.any_contains.imply.any_contains.limits_swap.apply(Eq[2], simplify=False)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << Eq[-1].subs(Eq.B_definition)


if __name__ == '__main__':
    run()

