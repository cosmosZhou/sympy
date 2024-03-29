from sympy import Set, symbols
from sympy.core import Basic, Expr
from sympy.multipledispatch import dispatch
from sympy.sets import Interval

_x, _y = symbols("x y")


@dispatch(Basic, Basic)
def _set_mul(x, y):
    return None

@dispatch(Set, Set)
def _set_mul(x, y):
    return None

@dispatch(Expr, Expr)
def _set_mul(x, y):
    return x*y

@dispatch(Interval, Interval)
def _set_mul(x, y):
    """
    Multiplications in interval arithmetic
    https://en.wikipedia.org/wiki/Interval_arithmetic
    """
    # TODO: some intervals containing 0 and oo will fail as 0*oo returns nan.
    comvals = (
        (x.start * y.start, bool(x.left_open or y.left_open)),
        (x.start * y.stop, bool(x.left_open or y.right_open)),
        (x.stop * y.start, bool(x.right_open or y.left_open)),
        (x.stop * y.stop, bool(x.right_open or y.right_open)),
    )
    # TODO: handle symbolic intervals
    minval, minopen = min(comvals)
    maxval, maxopen = max(comvals)
    return Interval(minval,maxval,
                    left_open=minopen, right_open=maxopen)
    return SetExpr(Interval(start, end))


@dispatch(Basic, Basic)
def _set_div(x, y):
    return None

@dispatch(Expr, Expr)
def _set_div(x, y):
    return x/y

@dispatch(Set, Set)
def _set_div(x, y):
    return None

@dispatch(Interval, Interval)
def _set_div(x, y):
    """
    Divisions in interval arithmetic
    https://en.wikipedia.org/wiki/Interval_arithmetic
    """
    from sympy.sets.setexpr import set_mul
    from sympy import oo
    if (y.start*y.stop).is_negative:
        return Interval(-oo, oo)
    if y.start == 0:
        s2 = oo
    else:
        s2 = 1/y.start
    if y.stop == 0:
        s1 = -oo
    else:
        s1 = 1/y.stop
    return set_mul(x, Interval(s1, s2, left_open=y.right_open, right_open=y.left_open))
