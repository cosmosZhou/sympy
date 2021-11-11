from util import *



@apply
def apply(given, s=None):
    assert given.is_NotElement

    e, S = given.args
    assert S.is_Union
    if s is None:
        s = S.args[0]
    else:
        assert s in S.args

    return NotElement(e, s)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(NotElement(x, A | B))

    Eq << sets.notin.imply.et.split.union.apply(Eq[0], simplify=None)




if __name__ == '__main__':
    run()

# created on 2021-06-09
# updated on 2021-06-09
