from util import *


@apply
def apply(self, var=None):
    if var is None:
        var = self.wrt
    assert var.is_symbol
    assert not var.is_given
    assert self._has(var)
    
    _var = var.unbounded
    domain = var.domain
    if domain.is_Interval:
        if domain.stop == oo:
            if domain.left_open:
                cond = _var > domain.start
            else:
                cond = _var >= domain.start
        elif domain.start == oo:
            if domain.right_open:
                cond = _var < domain.stop
            else:
                cond = _var <= domain.stop
    else:
        cond = Contains(_var, var.domain)
    return Suffice(cond, self._subs(var, _var))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(positive=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(x) > 0, x)

    Eq << algebra.cond.imply.all.apply(Eq[0])

    Eq << algebra.all.imply.suffice.apply(Eq[-1])


if __name__ == '__main__':
    run()