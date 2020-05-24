from sympy.utility import plausible
from sympy.core.relational import Equality, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan

from sympy import Symbol

from sympy import cos, pi
from sympy.sets.sets import Interval
from sympy.concrete.expr_with_limits import Exists


def extract(x_constraint, y_constraint, z_constraint):
    if isinstance(x_constraint, LessThan):
        x, z = x_constraint.args
    elif isinstance(x_constraint, GreaterThan):
        z, x = x_constraint.args
    else:
        return None

    if isinstance(y_constraint, LessThan):
        y, _z = y_constraint.args
    elif isinstance(y_constraint, GreaterThan):
        _z, y = y_constraint.args
    else:
        return None

    if _z != z:
        return None

    if isinstance(z_constraint, StrictLessThan):
        _z, x_y = z_constraint.args
    elif isinstance(z_constraint, StrictGreaterThan):
        x_y, _z = z_constraint.args
    else:
        return None

    if _z != z:
        return None

    if x_y != x + y:
        return None

    if x > 0 and y > 0:
        return x, y, z

    return None


@plausible
def apply(*given):
    x, y, z = extract(*given)

    theta = Symbol("theta")
    return Exists(Equality(z ** 2, x ** 2 + y ** 2 - 2 * x * y * cos(theta)), (theta, Interval(pi / 3, pi, right_open=True)), given=given)


from sympy.utility import check


@check
def prove(Eq):
    x = Symbol("x", positive=True)
    y = Symbol("y", positive=True)
    z = Symbol("z", positive=True)
    x_constraint = x <= z
    y_constraint = y <= z
    z_constraint = z < x + y
    
    Eq << apply(x_constraint, y_constraint, z_constraint)

    theta, *_ = Eq[-1].function.free_symbols - {x, y, z}

    Eq << Eq[-1].function.solve(cos(theta))

    Eq << Eq[-1].subs(z_constraint)
    Eq << Eq[-1] * (2 * x * y) - x * y + z ** 2

    Eq << Eq[-1].subs(x_constraint, y_constraint)


if __name__ == '__main__':
    prove(__file__)
