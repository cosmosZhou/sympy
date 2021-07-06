from util import *


@apply
def apply(self):
    expr, (i,_a, a1) = self.of(Sum)
    a = a1 - 1
    assert _a == -a
    return Equal(self, Sum[i:-a:a + 1](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, nonnegative=True, given=False)
    f = Function.f(real=True)
    Eq << apply(Sum[i:-n:n + 1](f(i)))

    Eq << Eq[-1] - Eq[-1].rhs

    


if __name__ == '__main__':
    run()
from . import infinity