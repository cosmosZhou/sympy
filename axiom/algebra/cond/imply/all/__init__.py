from util import *


def all(self, x):
    assert not x.is_given
    assert self._has(x)

    _x = x.unbounded
    return All(self._subs(x, _x), (_x, x.domain))

@apply
def apply(given, var=None):
    if var is None:
        var = given.wrt
    assert var.is_symbol
    return all(given, var)


@prove(provable=False)
def prove(Eq):
    from axiom import algebra

    e = Symbol(positive=True)
    f = Function(shape=(), integer=True)
    Eq << apply(f(e) > 0)

    Eq << algebra.all.given.ou.apply(Eq[1])




if __name__ == '__main__':
    run()

from . import restrict
from . import subs
from . import domain_defined
