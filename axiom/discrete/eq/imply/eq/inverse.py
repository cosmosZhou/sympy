from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    assert lhs.shape
    assert lhs.is_invertible or rhs.is_invertible
    return Equal(lhs.inverse(), rhs.inverse())    


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(real=True, shape=(n, n))
    B = Symbol.B(real=True, shape=(n, n), singular=False)
    Eq << apply(Equal(A, B))

    Eq << Eq[-1].subs(Eq[0])

    

    Eq << discrete.eq.imply.eq.det.apply(Eq[0])
    Eq << Unequal(Det(B), 0, plausible=True)
    
    Eq << algebra.eq.ne.imply.ne.transit.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
