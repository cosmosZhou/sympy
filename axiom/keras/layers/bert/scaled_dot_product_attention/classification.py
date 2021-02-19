
from axiom.utility import prove, apply
from sympy.core.relational import Equality
import sympy
from tensorflow.nn import softmax
from sympy import Symbol


@apply
def apply(n, d, i):
    Q = Symbol.Q(shape=(n, d), real=True)
    K = Symbol.K(shape=(n, d), real=True)
    V = Symbol.V(shape=(n, d), real=True)
    
    z = Symbol.z(shape=(n, d), definition=softmax(Q @ K.T / sympy.sqrt(d)) @ V)

    return Equality(z[i], softmax(Q[i] @ K.T / sympy.sqrt(d)) @ V)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol("d_z", integer=True)
    i = Symbol.i(integer=True)
    Eq << apply(n, d, i)
    
    M = Symbol.M(shape=(n, n), definition=Eq[0].rhs.args[0].arg)
    Eq << M.this.definition
    
    Eq << Eq[0].subs(Eq[-1].reversed)
    
    Eq << Eq[-1][i]
    
    Eq << Eq[2][i]
    
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)
