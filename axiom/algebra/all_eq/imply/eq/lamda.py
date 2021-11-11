from util import *


@apply
def apply(given):
    from sympy.concrete.limits import limits_dict
    function, *limits = given.of(All)
    function.of(Equal)

    dic = limits_dict(limits)
    assert len(dic) == 1
    (x, domain), *_ = dic.items()
    assert domain.is_Range

    lhs, rhs = function.args
    return Equal(Lamda[x:domain](lhs).simplify(), Lamda[x:domain](rhs).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), integer=True)

    Eq << apply(All[i:n](Equal(f(i), g(i))))

    i_ = Symbol.i(domain=Range(n))

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], i, i_)

    Eq << Eq[1].this.lhs.limits_subs(i, i_)

    Eq << Eq[-1].this.rhs.limits_subs(i, i_)


if __name__ == '__main__':
    run()

# created on 2019-01-08
# updated on 2019-01-08
