from util import *

import axiom
from axiom.algebra.ge.le.imply.le.quadratic import quadratic_coefficient


@apply
def apply(given, x=None):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    a, b, c = quadratic_coefficient(fx, x=x)
    assert a.is_zero == False
    delta = b * b - 4 * a * c

    return Or(Equal(x, (-b + sqrt(delta)) / (a * 2)), Equal(x, (-b - sqrt(delta)) / (a * 2)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(complex=True, zero=False)
    b = Symbol.b(complex=True, given=True)
    c = Symbol.c(complex=True, given=True)
    Eq << apply(Equal(a * x ** 2 + b * x + c, 0), x=x)

    Eq << Unequal(a, 0, plausible=True)

    Eq << algebra.is_nonzero.eq.imply.ou.quadratic.apply(Eq[-1], Eq[0], x=x, simplify=False)

if __name__ == '__main__':
    run()
