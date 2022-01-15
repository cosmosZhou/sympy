from util import *



@apply
def apply(imply):
    function, *limits = imply.of(Any)
    assert all(len(limit) == 1 for limit in limits)
    return function


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(real=True)
    f = Function(integer=True)
    Eq << apply(Any[e](f(e) > 0))

    Eq << algebra.cond.imply.any.apply(Eq[1], wrt=e)


if __name__ == '__main__':
    run()


from . import subs
# created on 2018-12-02
