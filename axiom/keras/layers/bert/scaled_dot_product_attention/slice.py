from util import *


@apply
def apply(n, d, index):
    Q = Symbol.Q(shape=(n, d), real=True)
    K = Symbol.K(shape=(n, d), real=True)
    V = Symbol.V(shape=(n, d), real=True)
    
    z = Symbol.z(softmax(Q @ K.T / sqrt(d)) @ V)

    return Equal(z[index], softmax(Q[index] @ K.T / sqrt(d)) @ V)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol("d_z", integer=True)
#     i = Symbol.i(integer=True)
    h = Symbol.h(domain=Range(0, n + 1))
    Eq << apply(n, d, slice(0, h))
    
    M = Symbol.M(Eq[0].rhs.args[0].arg)
    Eq << M.this.definition
    
    Eq << Eq[0].subs(Eq[-1].reversed)
    
    Eq << Eq[-1][:h]
    
    Eq << Eq[2][:h]
    
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
