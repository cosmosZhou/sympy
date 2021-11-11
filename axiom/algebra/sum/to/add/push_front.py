from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    front = function._subs(i, a - 1)
#     b >= a => b >= a - 1
    assert b >= a
    return Equal(self, Sum[i:a - 1:b](function) - front, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    C = Symbol(etype=dtype.integer, given=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:1:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.split, cond={0})


if __name__ == '__main__':
    run()

# created on 2019-11-04
# updated on 2019-11-04
