from util import *


@apply
def apply(lt_zero, add_ge_zero, x=None):
    a = lt_zero.of(Expr < 0)
    b, (S[a], c) = add_ge_zero.of(Expr ** 2 - Expr * Expr * 4 >= 0)
    assert x.is_real and not x.is_given
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c < 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a < 0, b ** 2 - 4 * a * c >= 0, x=x)

    Eq.delta_is_nonnegative = algebra.ge_zero.imply.sqrt_ge_zero.apply(Eq[1])

    Eq << Eq.delta_is_nonnegative - b

    Eq << algebra.lt_zero.ge.imply.le.div.apply(Eq[0], Eq[-1])

    Eq << Eq[-1] / 2

    Eq << sets.le.imply.el.interval.apply(Eq[-1])

    Eq << sets.el.imply.el.relax.apply(Eq[-1], Reals, simplify=None)

    epsilon = Symbol(negative=True)
    Eq << sets.el.imply.el.add.apply(Eq[-1], epsilon, simplify=None)

    Eq << algebra.any.given.cond.subs.apply(Eq[2], x, Eq[-1].lhs)

    Eq << algebra.et.given.et.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Expr ** 2).apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Expr ** 2).apply(algebra.square.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.add.collect)

    Eq << Eq[-1].this.find(Symbol * Add).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Symbol * Add).apply(algebra.mul.to.add)

    Eq << Eq[-1] / epsilon

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[0] * epsilon
    
    Eq << algebra.gt_zero.ge_zero.imply.gt_zero.add.apply(Eq[-1], Eq.delta_is_nonnegative)

    


if __name__ == '__main__':
    run()
# created on 2022-04-02
