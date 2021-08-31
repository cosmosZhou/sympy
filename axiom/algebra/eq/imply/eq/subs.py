from util import *


@apply
def apply(given, old, new):
    assert given.is_Equal
    assert old.is_symbol
    assert old.is_given is None
#    old should not be a inductive symbol in mathematical induction proof!
    assert new in given.domain_defined(old)
    return given._subs(old, new)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(n,))
    x, y, b = Symbol(real=True, shape=(n,))
    a = Symbol(real=True)
    Eq << apply(Equal(f(x) * a, b), x, y)

    Eq << Eq[0].subs(x, y)


if __name__ == '__main__':
    run()
