from util import *



def extract(x_constraint, y_constraint, z_constraint):
    if isinstance(x_constraint, LessEqual):
        x, z = x_constraint.args
    elif isinstance(x_constraint, GreaterEqual):
        z, x = x_constraint.args
    else:
        return None

    if isinstance(y_constraint, LessEqual):
        y, _z = y_constraint.args
    elif isinstance(y_constraint, GreaterEqual):
        _z, y = y_constraint.args
    else:
        return None

    if _z != z:
        return None

    if isinstance(z_constraint, Less):
        _z, x_y = z_constraint.args
    elif isinstance(z_constraint, Greater):
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
    return Exists[theta:Interval(pi / 3, pi, right_open=True)](Equal(z ** 2, x ** 2 + y ** 2 - 2 * x * y * cos(theta)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(positive=True)
    y = Symbol.y(positive=True)
    z = Symbol.z(positive=True)
    x_constraint = x <= z
    y_constraint = y <= z
    z_constraint = z < x + y

    Eq << apply(x_constraint, y_constraint, z_constraint)

    x = Symbol("x", x / z)
    y = Symbol("y", y / z)

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

    Eq << Eq[-1].this.function / (z * z)

    Eq << Eq[-1].this.function - (Eq[-1].function.rhs.args[-1] + 1)

    Eq.cos = Eq[-1].this.function / (2 * x * y)

    Eq << algebra.le.le.imply.le.quadratic.apply(Eq.x_bound, Eq.y_bound)

    Eq << Eq.xy_bound * Eq.xy_bound

    Eq << Eq[-1].this.lhs.expand() - 1 - 2 * x * y

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].apply(sets.gt.le.imply.contains.interval)

    Eq << sets.contains.imply.contains.interval.div.apply(Eq[-1], 2 * x * y)

    Eq << sets.contains.imply.contains.interval.acos.apply(Eq[-1])

    Eq << algebra.any.given.any.subs.apply(Eq.cos, Eq.cos.variable, Eq[-1].lhs)

    Eq << algebra.any.given.cond.apply(Eq[-1])

# https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F
if __name__ == '__main__':
    run()
