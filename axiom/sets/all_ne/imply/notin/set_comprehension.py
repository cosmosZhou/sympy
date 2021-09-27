from util import *


@apply
def apply(given):
    (xi, y), (i, n) = given.of(All[Unequal, Tuple[0]])
    if not xi._has(i):
        xi, y = y, xi

    x = Lamda[i:n](xi).simplify()

    return NotElement(y, x.set_comprehension())


@prove
def prove(Eq):
    from axiom import sets

    i = Symbol(integer=True)
    y = Symbol(real=True, given=True)
    x = Symbol(real=True, shape=(oo,), given=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(All[i:n](Unequal(x[i], y)))

    Eq << ~Eq[-1]

    Eq << sets.el_cup.imply.any_el.apply(Eq[-1])
    Eq << Eq[-1].this.expr.reversed

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
