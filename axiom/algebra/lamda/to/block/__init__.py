from util import *


@apply
def apply(self):
    function, *limits, (x, a, b) = self.of(Lamda)
    diff = b - a
    if not diff.is_Number:
        return self

    if limits:
        return

    assert function.shape
    array = []
    for i in range(diff):
        array.append(function._subs(x, sympify(i)))

    return Equal(self, BlockMatrix(array, shape=self.shape))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    n = 4
    a = Symbol(real=True, shape=(oo, n))
    Eq << apply(Lamda[i:n](a[i]))

    A = Symbol(Eq[0].lhs)
    B = Symbol(Eq[0].rhs)
    j = 0
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    j += 1
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    j += 1
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    j += 1
    Eq << Equal(A[j], B[j], plausible=True)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq.all_et = All[i:4](Equal(A[i], B[i]), plausible=True)

    Eq << Eq.all_et.this.apply(algebra.all.to.et.doit)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[-1])

    _i = Symbol('i', domain=Range(4))
    Eq << Eq.all_et.limits_subs(i, _i)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (_i, 0, 4))

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    run()
# created on 2019-10-16
from . import pop_front
from . import pop_back
from . import split
