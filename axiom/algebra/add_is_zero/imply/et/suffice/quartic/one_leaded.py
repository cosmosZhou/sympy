from util import *


def quartic_coefficient(fx, x):
    fx = fx.as_poly(x)
    if fx.degree() != 4:
        return None
    a = fx.nth(4)
    b = fx.nth(3)
    c = fx.nth(2)
    d = fx.nth(1)
    e = fx.nth(0)
    return a, b, c, d, e

@apply
def apply(given, x=None):
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    
    _1, a, b, c, d = quartic_coefficient(fx, x=x)
    assert _1 == 1
    return Suffice(Equal(a, 0), Equal(b, 0))
            


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, c, d = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 4 + a * x ** 3 + b * x ** 2 + c * x + d, 0), x=x)

    x = Symbol(x + a / 4)
    Eq.x_def = x.this.definition

    Eq << Eq.x_def.this.apply(algebra.eq.transposition, rhs=0).reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Pow[Add]).apply(algebra.pow.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq << algebra.add_is_zero.imply.et.suffice.quartic.withno_cubic.apply(Eq[-1], x)


if __name__ == '__main__':
    run()