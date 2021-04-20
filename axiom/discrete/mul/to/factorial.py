from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import discrete


@apply
def apply(self):
    n, factorial_n_1 = axiom.is_Mul(self)    
    n_1 = axiom.is_Factorial(factorial_n_1)
     
    assert n_1 == n - 1
    assert n > 0
    
    return Equal(self, factorial(n))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n * factorial(n - 1))
    
    Eq << Eq[0].this.rhs.apply(discrete.factorial.to.mul)


if __name__ == '__main__':
    prove()
