from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, statistics


# given: x | y & z = x | y
# imply: x | z = x
@apply
def apply(given):
    assert given.is_Equal
    lhs, rhs = given.args
    assert lhs.is_Conditioned and rhs.is_Conditioned
    yk, xy_historic = lhs.args
    _yk, y_k_1 = rhs.args
    
    assert yk == _yk
    y, k = yk.args
    assert y_k_1 == y[k - 1].as_boolean()
    
    x_historic, y_historic = xy_historic.args
    if y[:k].as_boolean() != y_historic:
        x_historic, y_historic = y_historic, x_historic
    assert y[:k].as_boolean() == y_historic
    
    return Equal(y[k] | y_historic, y[k] | y[k - 1])


@prove
def prove(Eq):
    d = Symbol.d(domain=Interval(2, oo, integer=True))
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), domain=Interval(0, d - 1, integer=True), random=True, given=True)
    
    k = Symbol.k(integer=True)
    
    Eq << apply(Equal(y[k] | (x[:k].as_boolean() & y[:k].as_boolean()), y[k] | y[k - 1]))

    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (k, 2, oo))
    
    Eq << Eq[-1].this().function.lhs.rhs.args[1].apply(algebra.eq.imply.et.split.block_matrix, Slice[-1:])

    Eq << statistics.eq.eq.given_deletion.single_condition_w.apply(Eq[-1], wrt=Eq[-1].lhs.rhs.args[1].lhs)
    
    Eq << Eq[1].apply(algebra.cond.given.et.forall, cond=k >= 2)
    
    Eq << Eq[-1].this().function.lhs.rhs.apply(algebra.eq.given.et.split.block_matrix, Slice[-1:])

    
if __name__ == '__main__':
    prove()
