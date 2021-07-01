from util import *


@apply(given=None)
def apply(self):
    r, (p, q) = self.of(Suffice[Suffice])    
    return Equivalent(self, Suffice(r, Suffice(p, q & r)))

@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol.n(integer=True, nonnegative=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)
    Eq << apply(Suffice(Contains(n, C), Suffice(Contains(n, A), Contains(n, B))))

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.swap)

    Eq << Eq[-1].this.rhs.rhs.rhs.apply(sets.contains.to.et.st.intersection)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.swap)


if __name__ == '__main__':
    run()