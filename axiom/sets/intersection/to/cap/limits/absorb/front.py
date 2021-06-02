from util import *
import axiom

from axiom.algebra.add.to.sum.limits.absorb.front import absorb

@apply
def apply(self):
    return Equal(self, absorb(Cap, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(etype=dtype.integer)
    Eq << apply(Intersection(Cap[k:1 + i:n](f(k)), f(i), evaluate=False))

    Eq << Eq[-1].this.rhs.apply(sets.cap.to.intersection.dissect, {i})

if __name__ == '__main__':
    run()
