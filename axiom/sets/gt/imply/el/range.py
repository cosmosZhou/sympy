from util import *


@apply(simplify=None)
def apply(given):
    n, b = given.of(Greater)
    assert n.is_integer or n.is_extended_integer
    return Element(n, Range(b + 1, oo))


@prove
def prove(Eq):
    from axiom import algebra

    n, b = Symbol(integer=True, given=True)
    Eq << apply(n > b)

    Eq << Eq[-1].simplify()

    Eq << algebra.ge.given.gt.apply(Eq[-1])


if __name__ == '__main__':
    run()

