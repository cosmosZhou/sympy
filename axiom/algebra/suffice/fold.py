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

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    C = Symbol.C(etype=dtype.real)
    Eq << apply(Suffice(Contains(x, A) & Contains(y, B), Contains(z, C)), index=0, swap=True)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.flatten)


if __name__ == '__main__':
    run()