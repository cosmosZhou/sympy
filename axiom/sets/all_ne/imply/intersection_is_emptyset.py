from util import *


@apply
def apply(given):
    (xi, y), (i, n) = given.of(All[Unequal, Tuple[0]])
    if not xi._has(i):
        xi, y = y, xi
        
    x = Lamda[i:n](xi).simplify()
    
    return Equal({y} & x.set_comprehension(), y.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    i = Symbol.i(integer=True)
    y = Symbol.y(real=True, given=True)
    x = Symbol.x(real=True, shape=(oo,), given=True)
    n = Symbol.n(integer=True, positive=True, given=True)
    Eq << apply(All[i:n](Unequal(x[i], y)))

    Eq << sets.intersection_is_emptyset.given.notcontains.apply(Eq[1])

    Eq << sets.notcontains.given.all_notcontains.apply(Eq[-1])
    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()