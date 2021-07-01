from util import *


@apply
def apply(given, index=-1):
    args, rhs = given.of(Equal[FiniteSet])
    
    first = args[:index]
    second = args[index:]
    
    first = [Contains(lhs, rhs).simplify() for lhs in first]
    second = [Contains(lhs, rhs).simplify() for lhs in second]    

    return And(*first), And(*second)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    S = Symbol.S(etype=dtype.real)
    Eq << apply(Equal({a, b}, S))

    

    Eq << Contains(a, {a, b}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Contains(b, {a, b}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()

