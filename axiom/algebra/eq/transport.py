from util import *


def transport(Equal, given, lhs=-1, rhs=None):
    _lhs, _rhs = given.of(Equal)
    if rhs is None:
        [*_lhs] = _lhs.of(Add)
        try:
            x = _lhs.pop(lhs)
        except TypeError:
            x = _lhs[lhs]
            del _lhs[lhs]
            x = Add(*x)

        _lhs = Add(*_lhs)
        _rhs -= x
    else:
        [*_rhs] = _rhs.of(Add)
        try:
            x = _rhs.pop(rhs)
        except TypeError:
            x = _rhs[rhs]
            del _rhs[rhs]
            x = Add(*x)

        _rhs = Add(*_rhs)
        _lhs -= x

    assert x.is_finite
    return Equal(_lhs, _rhs, evaluate=False)


@apply(given=None)
def apply(given, lhs=-1, rhs=None):
    return Equivalent(given, transport(Equal, given, lhs=lhs, rhs=rhs), evaluate=False)


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)
    Eq << apply(Equal(x + a, y), lhs=-1)

    Eq << Eq[-1].this.rhs + x


if __name__ == '__main__':
    run()
# created on 2018-05-16
