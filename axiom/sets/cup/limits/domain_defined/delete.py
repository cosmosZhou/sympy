from util import *

from axiom.algebra.sum.limits.domain_defined.delete import limits_delete
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    assert self.is_Cup
    return Equal(self, limits_delete(self))


@prove
def prove(Eq):
    from axiom import sets
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k,), integer=True)

    f = Function.f(etype=dtype.integer)
    h = Function.h(etype=dtype.real)

    Eq << apply(Cup[j:f(i), i:0:k](h(x[i], j)))

    s = Symbol.s(Cup[j:f(i)](h(x[i], j)))
    Eq << s.this.definition

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (i, 0, k))

    Eq << Eq[-1].this.lhs.function.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

