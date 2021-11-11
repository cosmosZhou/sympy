from util import *


@apply
def apply(eq, interval, x=None):
    fx, f_x = eq.of(Equal)
    assert f_x._subs(x, -x) == fx

    return Equal(Inf[x:-interval](fx), Inf[x:interval](fx))


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(f(x), f(-x)), Interval(m, M, right_open=True), x)

    y = Symbol(Eq[1].rhs)
    Eq << y.this.definition

    Eq <<= algebra.eq.imply.et.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed)

    z = Symbol(real=True)
    Eq <<= algebra.inf_le.imply.all_any_lt.apply(Eq[-3], z), algebra.inf_ge.imply.all_ge.apply(Eq[-2]), algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= Eq[-4].this.expr.apply(algebra.any.imply.any.limits.negate), algebra.all.imply.all.limits.subs.negate.real.apply(Eq[-3], x, -x), algebra.inf_le.given.all_any_lt.apply(Eq[-2], z), algebra.inf_ge.given.all_ge.apply(Eq[-1])

    Eq << Eq[-2].subs(Eq[0])
    Eq << Eq[-1].subs(Eq[0])



if __name__ == '__main__':
    run()
# created on 2019-04-08
# updated on 2019-04-08
