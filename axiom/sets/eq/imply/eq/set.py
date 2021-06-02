


from util import *
import axiom

# given : A & B = A | B => A = B


@apply
def apply(given):
    A, B = given.of(Equal)
    return Equal(FiniteSet(A), FiniteSet(B))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Equal(A, B))
    
    Eq << Eq[-1].subs(Eq[0])

if __name__ == '__main__':
    run()

