from sympy import Set, symbols, exp, log, S, Wild
from sympy.core import Expr, Add
from sympy.core.function import Lambda
from sympy.core.mod import Mod
from sympy.logic.boolalg import true
from sympy.multipledispatch import dispatch
from sympy.sets import (imageset, Interval, FiniteSet, Union, ImageSet,
                        EmptySet, Intersection, Range)

_x, _y = symbols("x y")

FunctionUnion = Lambda


@dispatch(FunctionUnion, FiniteSet)
def _set_function(f, x):
    return FiniteSet(*map(f, x))

@dispatch(Lambda, Interval)
def _set_function(f, x):
    from sympy.functions.elementary.miscellaneous import Min, Max
    from sympy.solvers.solveset import solveset
    from sympy.core.function import diff, Lambda
    from sympy.series import limit
    from sympy.calculus.singularities import singularities
    from sympy.sets import Complement
    # TODO: handle functions with infinitely many solutions (eg, sin, tan)
    # TODO: handle multivariate functions

    expr = f.expr
    if len(expr.free_symbols) > 1 or len(f.variables) != 1:
        return
    var = f.variables[0]

    if expr.is_Piecewise:
        result = EmptySet()
        domain_set = x
        for (p_expr, p_cond) in expr.args:
            if p_cond is true:
                intrvl = domain_set
            else:
                intrvl = p_cond.as_set()
                intrvl = Intersection(domain_set, intrvl)

            if p_expr.is_Number:
                image = FiniteSet(p_expr)
            else:
                image = imageset(Lambda(var, p_expr), intrvl)
            result = Union(result, image)

            # remove the part which has been `imaged`
            domain_set = Complement(domain_set, intrvl)
            if domain_set.is_EmptySet:
                break
        return result

    if not x.start.is_comparable or not x.stop.is_comparable:
        return

    try:
        sing = [i for i in singularities(expr, var)
            if i.is_real and i in x]
    except NotImplementedError:
        return

    if x.left_open:
        _start = limit(expr, var, x.start, dir=1)
    elif x.start not in sing:
        _start = f(x.start)
    if x.right_open:
        _end = limit(expr, var, x.stop, dir=-1)
    elif x.stop not in sing:
        _end = f(x.stop)

    if len(sing) == 0:
        solns = list(solveset(diff(expr, var), var))

        extr = [_start, _end] + [f(i) for i in solns
                                 if i.is_real and i in x]
        start, end = Min(*extr), Max(*extr)

        left_open, right_open = False, False
        if _start <= _end:
            # the minimum or maximum value can occur simultaneously
            # on both the edge of the interval and in some interior
            # point
            if start == _start and start not in solns:
                left_open = x.left_open
            if end == _end and end not in solns:
                right_open = x.right_open
        else:
            if start == _end and start not in solns:
                left_open = x.right_open
            if end == _start and end not in solns:
                right_open = x.left_open

        return Interval(start, end, left_open=left_open, right_open=right_open)
    else:
        return imageset(f, Interval(x.start, sing[0], left_open=x.left_open, right_open=True)) + \
            Union(*[imageset(f, Interval(sing[i], sing[i + 1], left_open=True, right_open=True))
                    for i in range(0, len(sing) - 1)]) + \
            imageset(f, Interval(sing[-1], x.stop, left_open=True, right_open=x.right_open))

@dispatch(FunctionUnion, Union)
def _set_function(f, x):
    return Union(*(imageset(f, arg) for arg in x.args))

@dispatch(FunctionUnion, Intersection)
def _set_function(f, x):
    from sympy.sets.sets import is_function_invertible_in_set
    # If the function is invertible, intersect the maps of the sets.
    if is_function_invertible_in_set(f, x):
        return Intersection(*(imageset(f, arg) for arg in x.args))
    else:
        return ImageSet(Lambda(_x, f(_x)), x)

@dispatch(FunctionUnion, EmptySet)
def _set_function(f, x):
    return x

@dispatch(FunctionUnion, Set)
def _set_function(f, x):
    return ImageSet(Lambda(_x, f(_x)), x)

@dispatch(FunctionUnion, Range)
def _set_function(f, self):
    from sympy.core.function import expand_mul
    if not self:
        return EmptySet()
    if not isinstance(f.expr, Expr):
        return
    if self.size == 1:
        return FiniteSet(f(self[0]))
    if f is S.IdentityFunction:
        return self

    x = f.variables[0]
    expr = f.expr
    # handle f that is linear in f's variable
    if x not in expr.free_symbols or x in expr.diff(x).free_symbols:
        return
    if self.start.is_finite:
        F = f(self.step*x + self.start)  # for i in range(len(self))
    else:
        F = f(-self.step*x + self[-1])
    F = expand_mul(F)
    if F != expr:
        return imageset(x, F, Range(self.size))

@dispatch(FunctionUnion, Interval)
def _set_function(f, self):
    if self.is_integer:
        #for positive integers:
        if self.args == (1, S.Infinity, 1):    
            expr = f.expr
            if not isinstance(expr, Expr):
                return
        
            x = f.variables[0]
            if not expr.free_symbols - {x}:
                step = expr.coeff(x)
                c = expr.subs(x, 0)
                if c.is_Integer and step.is_Integer and expr == step*x + c:
                    if self is S.Naturals:
                        c += step
                    if step > 0:
                        return Range(c, S.Infinity, step)
                    return Range(c, S.NegativeInfinity, step)
            return
        
        expr = f.expr
        if not isinstance(expr, Expr):
            return
    
        n = f.variables[0]
    
        # f(x) + c and f(-x) + c cover the same integers
        # so choose the form that has the fewest negatives
        c = f(0)
        fx = f(n) - c
        f_x = f(-n) - c
        neg_count = lambda e: sum(_._coeff_isneg() for _ in Add.make_args(e))
        if neg_count(f_x) < neg_count(fx):
            expr = f_x + c
    
        a = Wild('a', exclude=[n])
        b = Wild('b', exclude=[n])
        match = expr.match(a*n + b)
        if match and match[a]:
            # canonical shift
            b = match[b]
            if abs(match[a]) == 1:
                nonint = []
                for bi in Add.make_args(b):
                    if not bi.is_integer:
                        nonint.append(bi)
                b = Add(*nonint)
            if b.is_number and match[a].is_real:
                mod = b % match[a]
                reps = dict([(m, m.args[0]) for m in mod.atoms(Mod)
                    if not m.args[0].is_real])
                mod = mod.xreplace(reps)
                expr = match[a]*n + mod
            else:
                expr = match[a]*n + b
    
        if expr != f.expr:
            return ImageSet(Lambda(n, expr), S.Integers)

