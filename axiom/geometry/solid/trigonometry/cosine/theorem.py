from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, sets


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


@apply
def apply(*given):
    x, y, z = extract(*given)

    theta = Symbol.theta(real=True)
    return Exists[theta:Interval(pi / 3, pi, right_open=True)](Equality(z ** 2, x ** 2 + y ** 2 - 2 * x * y * cos(theta)))


@prove
def prove(Eq):
    x = Symbol.x(positive=True)
    y = Symbol.y(positive=True)
    z = Symbol.z(positive=True)
    x_constraint = x <= z
    y_constraint = y <= z
    z_constraint = z < x + y
        
    Eq << apply(x_constraint, y_constraint, z_constraint)
    
    x = Symbol("x", definition=x / z)
    y = Symbol("y", definition=y / z)
    
    Eq << x.this.definition * z
    Eq.x_definition = Eq[-1].reversed
    Eq << y.this.definition * z
    Eq.y_definition = Eq[-1].reversed

    Eq << Eq[0] / z 
    
    Eq.x_bound = Eq[-1].subs(Eq.x_definition)
    
    Eq << Eq[1] / z
    
    Eq.y_bound = Eq[-1].subs(Eq.y_definition)
    
    Eq << Eq[2] / z
    
    Eq << Eq[-1].reversed
    
    Eq << Eq[-1].subs(Eq.x_definition, Eq.y_definition)
    
    Eq.xy_bound = Eq[-1].this.lhs.ratsimp()
    
    Eq << Eq[3].this.function.subs(Eq.x_definition, Eq.y_definition)
    
    Eq << Eq[-1] / (z * z)
    
    Eq << Eq[-1] - Eq[-1].function.rhs.args[-1] - 1
    
    Eq.cos = Eq[-1] / (2 * x * y)

    Eq << algebre.less_than.less_than.imply.less_than.quadratic.apply(Eq.x_bound, Eq.y_bound)
    
    Eq << Eq.xy_bound * Eq.xy_bound
    
    Eq << Eq[-1].this.lhs.expand() - 1 - 2 * x * y
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << Eq[-1].apply(sets.strict_greater_than.less_than.imply.contains)
    
    Eq << Eq[-1] / (2 * x * y)
    
    Eq << Eq[-1].subs(Eq.cos.reversed)

    Eq << algebre.imply.forall.limits_assert.apply(Eq[-1].limits)
    
    Eq << Eq[-1].this.function.cos()
    
    Eq << Unequal(Eq[-2].function.rhs, EmptySet(etype=dtype.real), plausible=True)
    
    Eq << sets.is_nonemptyset.forall.imply.exists.apply(Eq[-1], Eq[-2])
    

if __name__ == '__main__':
    prove(__file__)
