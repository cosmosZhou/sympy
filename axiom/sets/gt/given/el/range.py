from util import *


@apply(simplify=False)
def apply(given):
    n, b = given.of(Greater)
    assert n.is_integer
    return Element(n, Range(b + 1, oo))


@prove
def prove(Eq):
    from axiom import algebra
    n, b = Symbol(integer=True, given=True)

    Eq << apply(n > b)

    Eq << Eq[-1].simplify()

    Eq << algebra.gt.given.ge.apply(Eq[0])



if __name__ == '__main__':
    run()

# created on 2021-04-14
# updated on 2021-04-14
