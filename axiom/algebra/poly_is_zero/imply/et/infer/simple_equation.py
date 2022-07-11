from util import *


@apply
def apply(given, x):
    fx = given.of(Equal[0])
    assert fx._has(x)
    if x.is_Symbol:
        x_ = x
    else:
        x, x_ = Dummy('x', **x.type.dict), x
        fx = fx._subs(x_, x)

    p = fx.as_poly(x)
    assert p.degree() == 1
    a = p.nth(1)
    b = p.nth(0)
    return Infer(Equal(a, 0), Equal(b, 0)), Infer(Unequal(a, 0), Equal(x_, -b / a))

@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(Equal(a * x + b, 0), x=x)

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[0], cond=Equal(a, 0))

    Eq <<= algebra.infer.imply.infer.et.apply(Eq[-2]), Eq[-1].this.rhs.apply(algebra.eq.transport, lhs=0)

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.cond.imply.cond.subs), algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.eq.imply.eq.div)


if __name__ == '__main__':
    run()
# created on 2018-08-16
