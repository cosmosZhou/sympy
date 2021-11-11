from util import *


@apply
def apply(given):
    or_eqs = given.of(Or)

    args = []
    for eq in or_eqs:
        lhs, rhs = eq.of(Equal)
        args.append(lhs - rhs)
    mul = Mul(*args)
    return Equal(mul, ZeroMatrix(*mul.shape))


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, p = Symbol(real=True, shape=(k,), given=True)
    f, g, h = Function(shape=(k,), real=True)
    Eq << apply(Equal(p, f(x)) | Equal(p, g(x)) | Equal(p, h(x)))

    Eq <<= ~Eq[1] & Eq[0]

    Eq << Eq[-1].this.args[0].apply(algebra.ne_zero.imply.et.matrix)

    Eq << Eq[-1].this.args[0].apply(algebra.ne_zero.imply.et.matrix)

    Eq << algebra.et.imply.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-01-26
# updated on 2018-01-26
