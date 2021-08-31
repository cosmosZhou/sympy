from util import *


def piece_together(Sum, self):
    function = []
    limits = None
    for arg in self.args:
        assert isinstance(arg, Sum)

        if limits is None:
            limits = arg.limits
            func = arg.expr
        else:
            i = -1
            while i >= -len(limits) and i >= -len(arg.limits):
                if limits[i] == arg.limits[i]:
                    i -= 1
                    continue
                else:
                    break

            i += 1

            assert i < 0

            inner_limits, limits = limits[:i], limits[i:]
            _inner_limits = arg.limits[:i]

            if inner_limits:
                function = [Sum(f, *inner_limits) for f in function]

            if _inner_limits:
                func = Sum(arg.expr, *_inner_limits)
            else:
                func = arg.expr

        function.append(func)

    return Sum(self.func(*function), *limits)

@apply
def apply(self):
    assert self.is_Add

    return Equal(self, piece_together(Sum, self))


@prove
def prove(Eq):
    from axiom import algebra
    i, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Sum[i:k, k:n](f(k, i)) + Sum[k:n](g(k)))

    Eq << Eq[0].this.rhs.apply(algebra.sum.to.add)


if __name__ == '__main__':
    run()

from . import limits
from . import sub
