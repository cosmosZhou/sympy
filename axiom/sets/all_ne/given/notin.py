from util import *


@apply
def apply(imply):
    (x, y), (lhs, *rhs) = imply.of(All[Unequal])
    if len(rhs) == 2:
        rhs = Range(*rhs) if lhs.is_integer else Interval(*rhs)
    else:
        [rhs] = rhs

    if x == lhs:
        return NotElement(y, rhs)
    if y == lhs:
        return NotElement(x, rhs)


@prove
def prove(Eq):
    from axiom import sets
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:n](Unequal(i, j)))

    Eq << sets.notin.imply.all_ne.apply(Eq[1], reverse=True)


if __name__ == '__main__':
    run()

# created on 2021-01-14
