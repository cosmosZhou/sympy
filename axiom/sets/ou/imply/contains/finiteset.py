from util import *



@apply
def apply(given):
    or_eqs = given.of(Or)

    common_term = None
    for eq in or_eqs:
        x, y = eq.of(Equal)
        if common_term is None:
            common_term = {x, y}
        else:
            common_term &= {x, y}
    if len(common_term) == 1:
        x, *_ = common_term

        rhs = set()
        for eq in or_eqs:
            s = {*eq.args}
            s.remove(x)
            rhs |= s

        return Contains(x, FiniteSet(*rhs))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    c = Symbol.c(real=True, given=True)

    Eq << apply(Equal(x, a) | Equal(x, b) | Equal(x, c))

    Eq << ~Eq[-1]

    Eq << sets.notcontains.imply.et.split.finiteset.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

