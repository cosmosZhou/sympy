from util import *


@apply(simplify=False)
def apply(given, expr=None):
    from sympy.concrete.limits import limits_dict
    eq, *limits = given.of(All)

    dic = limits_dict(limits)
    assert len(dic) == 1
    (x, domain), *_ = dic.items()
    assert domain.is_Range

    lhs, rhs = eq.of(Equal)
    if expr is not None:
        lhs, rhs = expr, expr._subs(lhs, rhs)
        
    return Equal(Lamda[x:domain](lhs).simplify(), Lamda[x:domain](rhs).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=True)
    i = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(All[i:n](Equal(f(i), g(i))))

    j = Symbol(domain=Range(n))
    Eq << algebra.all.imply.cond.subs.apply(Eq[0], i, j)

    Eq << Eq[1].this.lhs.limits_subs(i, j)

    Eq << Eq[-1].this.rhs.limits_subs(i, j)

    
    


if __name__ == '__main__':
    run()

# created on 2019-01-08
# updated on 2022-03-17
