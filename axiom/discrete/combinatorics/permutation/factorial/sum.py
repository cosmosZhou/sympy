from sympy import *
from axiom.utility import prove, apply
from axiom import discrete


@apply
def apply(n):
    i = Symbol.i(integer=True)
    return Equal(factorial(n), Sum[i:n + 1]((-1) ** (n - i) * i ** n * binomial(n, i)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n)

    x = Symbol.x(real=True)
    
    Eq << discrete.difference.definition.apply(x ** n, x, n)
    
    Eq << discrete.difference.factorial.apply(x, n)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].subs(x, 0)


if __name__ == '__main__':
    prove()
