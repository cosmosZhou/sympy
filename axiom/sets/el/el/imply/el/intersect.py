from util import *


@apply
def apply(contains1, contains2):
    assert contains1.is_Element
    assert contains2.is_Element

    e, A = contains1.args
    _e, B = contains2.args
    assert e == _e

    return Element(e, A & B)


@prove
def prove(Eq):
    e = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)

    Eq << apply(Element(e, A), Element(e, B))

    Eq <<= Eq[0] & Eq[1]


if __name__ == '__main__':
    run()

