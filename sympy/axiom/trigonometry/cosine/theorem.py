from sympy.utility import cout, Eq, plausible
from sympy.core.relational import Equality, StrictLessThan, StrictGreaterThan, \
    LessThan, GreaterThan

from sympy import exp, Symbol

from sympy import factorial, cos, pi
from sympy.sets.sets import Interval
from sympy.core.numbers import Infinitesimal, NegativeInfinitesimal, epsilon, oo
from sympy.functions.elementary.miscellaneous import Maximum
from sympy.core.add import Add
from sympy.logic.boolalg import plausibles_dict


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


def apply(*given):

    if given :
        x, y, z = extract(*given)
    else:
        x = Symbol("x", positive=True)
        y = Symbol("y", positive=True)
        z = Symbol("z", positive=True)

        x_constraint = x <= z
        y_constraint = y <= z
        z_constraint = z < x + y

        given = [x_constraint, y_constraint, z_constraint]

#     given.clauses()
    theta = Symbol("theta", domain=Interval(pi / 3, pi, right_open=True))
    return Equality(z ** 2, x ** 2 + y ** 2 - 2 * x * y * cos(theta),
                    with_clause=theta,
                    given=given,
                    plausible=plausible())


from sympy.utility import check
@check
def prove():
    cout << apply()
    x_constraint, y_constraint, z_constraint = Eq[-1].given
    x, y, z = extract(x_constraint, y_constraint, z_constraint)

    cout << Eq[-1].solve(Eq[-1].with_clause)

    cout << Eq[-1].cos()

    cout << Eq[-1].as_two_terms()

    cout << Eq[-2].subs(z_constraint)
    cout << Eq[-1] * (2 * x * y) - x * y + z ** 2

    cout << Eq[-1].subs(x_constraint, y_constraint)

    cout << (Eq[-2] & Eq[-3]).acos()

#     cout << (Eq[-1] & Eq[1])


if __name__ == '__main__':
    prove()

    print('plausibles_dict:')
    for index, eq in plausibles_dict(Eq).items():
        print("Eq[%d] : %s" % (index, eq))
