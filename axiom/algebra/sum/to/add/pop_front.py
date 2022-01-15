from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    front = function._subs(i, a)
#     b >= a => b + 1 >= a
    assert a + 1 <= b
    return Equal(self, Add(Sum[i:a + 1:b](function), front), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, h = Function(real=True)
    Eq << apply(Sum[i:0:n + 1](f(i) + h(i)))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split, cond={0})


if __name__ == '__main__':
    run()
# created on 2020-03-23
