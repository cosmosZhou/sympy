from util import *



# given: |S| = 1
# Sum[x:S](x) in S
@apply
def apply(given, var=None):
    assert given.is_Equal
    S_abs, one = given.args
    assert S_abs.is_Abs and one == 1
    S = S_abs.arg
    assert S.is_set
    if var is None:
        var = S.element_symbol()
        assert not var.is_set
    return Contains(Sum[var:S](var), S)




@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True)
    S = Symbol.A(etype=dtype.integer * n)

    Eq << apply(Equal(Abs(S), 1))

    Eq << sets.eq.imply.any_eq.one.apply(Eq[0]).reversed

    Eq <<= Eq[1] & Eq[-1]

    Eq << algebra.et.given.any_et.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.function.apply(algebra.et.given.et.subs.eq)


if __name__ == '__main__':
    run()

