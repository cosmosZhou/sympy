from util import *


@apply
def apply(given, *, cond=None):
    or_eqs = given.of(Or)

    new_or_eqs = []

    and_eqs = []
    for and_eq in or_eqs:
        if and_eq.is_And:
            try:
                i = and_eq.args.index(cond)
                args = [*and_eq.args]
                del args[i]
                and_eqs.append(And(*args))
                continue
            except:
                ...
        new_or_eqs.append(and_eq)

    assert not new_or_eqs
    assert and_eqs

    return cond, Or(*and_eqs)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    f, h, g = Function(real=True)
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y)) & (y > 0), Equal(h(x), g(y)) & (y > 0)), cond=y > 0)

    Eq << algebra.et.imply.ou.apply(Eq[1] & Eq[2], simplify=False)


if __name__ == '__main__':
    run()

# created on 2020-02-18
