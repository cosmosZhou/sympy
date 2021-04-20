from sympy.core.sympify import sympify


def series(expr, x=None, x0=0, n=6, dir=1):
    """Series expansion of expr around point `x = x0`.

    See the docstring of Expr.series() for complete details of this wrapper.
    """
    expr = sympify(expr)
    return expr.series(x, x0, n, dir)
