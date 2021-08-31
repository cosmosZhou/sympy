from util import *



@apply
def apply(given, j=None):
    assert given.is_Equal
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n
    x = Lamda(x_set_comprehension.expr.arg, *x_set_comprehension.limits).simplify()

    if j is None:
        j = Symbol.j(domain=Range(0, n))

    assert j >= 0 and j < n

    return Any[k:n](Equal(x[k], j))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(domain=Range(2, oo), given=True)
    x = Symbol(shape=(oo,), integer=True, given=True)
    k = Symbol(integer=True)
    j = Symbol(domain=Range(0, n), given=True)
    Eq << apply(Equal(x[:n].set_comprehension(k), Range(0, n)), j)

    Eq << ~Eq[-1]

    Eq << Eq[-1].reversed.this.expr.apply(sets.ne.imply.notin, simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.notin.imply.notin.cup, limit=(k, 0, n))

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
