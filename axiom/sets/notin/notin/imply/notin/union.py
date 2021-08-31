from util import *



@apply
def apply(notcontains1, notcontains2):
    assert notcontains1.is_NotElement
    assert notcontains2.is_NotElement

    e, A = notcontains1.args
    _e, B = notcontains2.args
    assert e == _e

    return NotElement(e, (A | B).simplify())


@prove
def prove(Eq):
    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(NotElement(e, A), NotElement(e, B))

    Eq <<= Eq[0] & Eq[1]


if __name__ == '__main__':
    run()

