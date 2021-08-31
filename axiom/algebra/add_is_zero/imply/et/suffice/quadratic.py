from util import *


@apply
def apply(given, x=None):
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    fx = given.of(Equal[0])
    
    x, a, b, c = quadratic_coefficient(fx, x=x)

    delta = b * b - 4 * a * c

    return Suffice(Equal(a, 0) & Equal(b, 0), Equal(c, 0)), Suffice(Equal(a, 0) & Unequal(b, 0), True if b == 0 else Equal(x, -c / b)), Suffice(Unequal(a, 0), Or(Equal(x, (-b + sqrt(delta)) / (a * 2)), Equal(x, (-b - sqrt(delta)) / (a * 2))))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b, c = Symbol(complex=True, given=True)
    Eq << apply(Equal(a * x ** 2 + b * x + c, 0))

    Eq << algebra.cond.imply.et.suffice.split.apply(Eq[0], cond=Equal(a, 0))

    Eq <<= algebra.suffice.imply.suffice.et.apply(Eq[-2]), algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.cond.imply.cond.subs), Eq[-1].this.rhs.apply(algebra.is_nonzero.eq.imply.ou.quadratic, x=x, simplify=False)

    Eq << Eq[-1].this.rhs.apply(algebra.add_is_zero.imply.et.suffice.simple_equation, x=x)

    Eq << algebra.suffice.imply.et.suffice.apply(Eq[-1])

    #Eq <<= Eq[-2].this.apply(algebra.suffice.flatten), Eq[-1].this.apply(algebra.suffice.flatten)


if __name__ == '__main__':
    run()
