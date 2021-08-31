from util import *


@apply(given=None)
def apply(self, index=0, swap=False):
    [*eqs], q = self.of(Suffice[And, Basic])

    r = eqs[index]
    if isinstance(r, list):
        r = And(*r)

    del eqs[index]
    p = And(*eqs)
    if swap:
        r, p = p, r

    return Equivalent(self, Suffice(r, Suffice(p, q)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True)
    A, B, C = Symbol(etype=dtype.real)
    Eq << apply(Suffice(Element(x, A) & Element(y, B), Element(z, C)), index=0, swap=True)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.flatten)


if __name__ == '__main__':
    run()
