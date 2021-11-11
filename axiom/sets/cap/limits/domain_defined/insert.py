from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.domain_defined.insert import limits_insert
    assert self.is_Cap
    return Equal(self, limits_insert(self))


@prove
def prove(Eq):
    from axiom import sets
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(etype=dtype.real)

    Eq << apply(Cap[j:f(i), i](h(x[i], j)))

    Eq << Eq[-1].this.rhs.apply(sets.cap.limits.domain_defined.delete)


if __name__ == '__main__':
    run()

# created on 2021-01-19
# updated on 2021-01-19
