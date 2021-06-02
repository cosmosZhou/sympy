from util import *
import axiom



@apply
def apply(imply):
    (x, y), *limits = imply.of(ForAll[Unequal])
    lhs, rhs = axiom.limit_is_set(limits)
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

    Eq << apply(ForAll[i:n](Unequal(i, j)))

    Eq << sets.notcontains.imply.all_ne.apply(Eq[1], reverse=True)


if __name__ == '__main__':
    run()

