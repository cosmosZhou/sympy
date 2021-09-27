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

        return Element(x, FiniteSet(*rhs))


@prove
def prove(Eq):
    from axiom import sets
    x, a, b, c = Symbol(real=True, given=True)

    Eq << apply(Equal(x, a) | Equal(x, b) | Equal(x, c))

    Eq << sets.el.imply.ou.split.finiteset.apply(Eq[-1])


if __name__ == '__main__':
    run()

