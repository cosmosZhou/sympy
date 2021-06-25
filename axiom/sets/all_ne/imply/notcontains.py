from util import *


@apply
def apply(given):
    (x, y), (lhs, *rhs) = given.of(All[Unequal])
    if len(rhs) == 2:
        rhs = Range(*rhs) if lhs.is_integer else Interval(*rhs)
    else:
        [rhs] = rhs
        
    if x == lhs:
        return NotContains(y, rhs)
    if y == lhs:
        return NotContains(x, rhs)


@prove
def prove(Eq):
    from axiom import sets
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True, given=True)
    n = Symbol.n(integer=True, positive=True, given=True)

    Eq << apply(All[i:n](Unequal(i, j)))

    Eq << ~Eq[-1]

    Eq << sets.contains.imply.any_eq.apply(Eq[-1], reverse=True)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

