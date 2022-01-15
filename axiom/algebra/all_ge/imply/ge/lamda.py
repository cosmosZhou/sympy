from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])
    return Lamda(lhs, *limits) >= Lamda(rhs, *limits)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(All[i:n](f(i) >= g(i)))
    
    Eq << ~Eq[1]
    
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2022-01-01