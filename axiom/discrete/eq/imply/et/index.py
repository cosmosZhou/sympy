from util import *


def index_function(n):
    k = Symbol(integer=True)

    def eval(*args):
        if len(args) == 3:
            x, a, (j,) = args
            j = a[j]
        else:
            x, (j,) = args

        return Lamda[k:n](KroneckerDelta(x[k], j)) @ Lamda[k:n](k)

    index = Function(shape=(), integer=True)
    index.eval = eval
    return index


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
        j = Symbol(domain=Range(0, n), given=True)

    assert j >= 0 and j < n

    index = index_function(n)
    index_j = index[j](x[:n], evaluate=False)
#     index_j = index[j](x[:n])
    return Element(index_j, Range(0, n)), Equal(x[index_j], j)


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(domain=Range(2, oo))

    x = Symbol(shape=(oo,), integer=True)

    k = Symbol(integer=True)

    j = Symbol(domain=Range(0, n), given=True)

    Eq << apply(Equal(x[:n].set_comprehension(k), Range(0, n)), j)

    a = Symbol(Lamda[k:n](k))
    Eq.aj_definition = a.this.definition[j]

    Eq << a.set_comprehension().this.expr.arg.base.definition

    Eq << Eq[-1].apply(sets.eq.imply.eq.card)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-2])

    Eq << discrete.eq.eq.imply.et.index_general.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-2].this.lhs.defun(), Eq[-1].this.lhs.indices[0].defun()

    Eq <<= Eq[-2].subs(Eq.aj_definition), Eq[-1].subs(Eq.aj_definition)

    Eq << Eq[1].this.lhs.defun()

    Eq << Eq[2].this.lhs.indices[0].defun()


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
