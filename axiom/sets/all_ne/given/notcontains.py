from util import *


@apply
def apply(imply):
    (x, y), (lhs, *rhs) = imply.of(All[Unequal])
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
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(All[i:n](Unequal(i, j)))

    Eq << sets.notcontains.imply.all_ne.apply(Eq[1], reverse=True)


if __name__ == '__main__':
    run()

