from util import *
import axiom



@apply
def apply(given, d):
    lhs, rhs = given.of(Equal)
    return Equal(lhs / d, rhs / d) | Equal(d, 0)


@prove
def prove(Eq):
    from axiom import algebra
    b = Symbol.b(real=True)
    a = Symbol.a(real=True)
    x = Symbol.x(domain=Interval(a, b), given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    d = Symbol.d(real=True, given=True)

    Eq << apply(Equal(f(x), g(x)), d)

    Eq << ~Eq[1]

    Eq << Eq[-1].apply(algebra.is_nonzero.ne.imply.ne.multiply)

    Eq <<= Eq[0] & Eq[-1]

if __name__ == '__main__':
    run()

