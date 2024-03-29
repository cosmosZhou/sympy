
from sympy.concrete.expr_with_limits import ExprWithLimits
from sympy.core.singleton import S


class ReorderError(NotImplementedError):
    """
    Exception raised when trying to reorder dependent limits.
    """

    def __init__(self, expr, msg):
        super(ReorderError, self).__init__(
            "%s could not be reordered: %s." % (expr, msg))


class ExprWithIntLimits(ExprWithLimits):

    def change_index(self, var, trafo, newvar=None):
        r"""
        Change index of a Sum or Product.

        Perform a linear transformation `x \mapsto a x + b` on the index variable
        `x`. For `a` the only values allowed are `\pm 1`. A new variable to be used
        after the change of index can also be specified.

        Usage
        =====

        ``change_index(expr, var, trafo, newvar=None)`` where ``var`` specifies the
        index variable `x` to transform. The transformation ``trafo`` must be linear
        and given in terms of ``var``. If the optional argument ``newvar`` is
        provided then ``var`` gets replaced by ``newvar`` in the final expression.

        Examples
        ========

        >>> from sympy import Sum, Product, simplify
        >>> from sympy.abc import x, y, a, b, c, d, u, v, i, j, k, l

        >>> S = Sum(x, (x, a, b))
        >>> S.doit()
        -a**2/2 + a/2 + b**2/2 + b/2

        >>> Sn = S.change_index(x, x + 1, y)
        >>> Sn
        Sum(y - 1, (y, a + 1, b + 1))
        >>> Sn.doit()
        -a**2/2 + a/2 + b**2/2 + b/2

        >>> Sn = S.change_index(x, -x, y)
        >>> Sn
        Sum(-y, (y, -b, -a))
        >>> Sn.doit()
        -a**2/2 + a/2 + b**2/2 + b/2

        >>> Sn = S.change_index(x, x+u)
        >>> Sn
        Sum(-u + x, (x, a + u, b + u))
        >>> Sn.doit()
        -a**2/2 - a*u + a/2 + b**2/2 + b*u + b/2 - u*(-a + b + 1) + u
        >>> simplify(Sn.doit())
        -a**2/2 + a/2 + b**2/2 + b/2

        >>> Sn = S.change_index(x, -x - u, y)
        >>> Sn
        Sum(-u - y, (y, -b - u, -a - u))
        >>> Sn.doit()
        -a**2/2 - a*u + a/2 + b**2/2 + b*u + b/2 - u*(-a + b + 1) + u
        >>> simplify(Sn.doit())
        -a**2/2 + a/2 + b**2/2 + b/2

        >>> P = Product(i*j**2, (i, a, b), (j, c, d))
        >>> P
        Product(i*j**2, (i, a, b), (j, c, d))
        >>> P2 = P.change_index(i, i+3, k)
        >>> P2
        Product(j**2*(k - 3), (k, a + 3, b + 3), (j, c, d))
        >>> P3 = P2.change_index(j, -j, l)
        >>> P3
        Product(l**2*(k - 3), (k, a + 3, b + 3), (l, -d, -c))

        When dealing with symbols only, we can make a
        general linear transformation:

        >>> Sn = S.change_index(x, u*x+v, y)
        >>> Sn
        Sum((-v + y)/u, (y, b*u + v, a*u + v))
        >>> Sn.doit()
        -v*(a*u - b*u + 1)/u + (a**2*u**2/2 + a*u*v + a*u/2 - b**2*u**2/2 - b*u*v + b*u/2 + v)/u
        >>> simplify(Sn.doit())
        a**2*u/2 + a/2 - b**2*u/2 + b/2

        However, the last result can be inconsistent with usual
        summation where the index increment is always 1. This is
        obvious as we get back the original value only for ``u``
        equal +1 or -1.

        See Also
        ========

        sympy.concrete.simplification.index,
        sympy.concrete.simplification.reorder_limit,
        sympy.concrete.simplification.reorder,
        sympy.concrete.simplification.reverse_order
        """
        if newvar is None:
            newvar = var

        limits = []
        for limit in self.limits:
            if limit[0] == var:
                p = trafo.as_poly(var)
                if p.degree() != 1:
                    raise ValueError("Index transformation is not linear")
                alpha = p.coeff_monomial(var)
                beta = p.coeff_monomial(S.One)
                if alpha.is_number:
                    if alpha == S.One:
                        limits.append((newvar, alpha * limit[1] + beta, alpha * limit[2] + beta))
                    elif alpha == S.NegativeOne:
                        limits.append((newvar, alpha * limit[2] + beta, alpha * limit[1] + beta))
                    else:
                        raise ValueError("Linear transformation results in non-linear summation stepsize")
                else:
                    # Note that the case of alpha being symbolic can give issues if alpha < 0.
                    limits.append((newvar, alpha * limit[2] + beta, alpha * limit[1] + beta))
            else:
                limits.append(limit)

        function = self.expr.subs(var, (var - beta) / alpha)
        function = function.subs(var, newvar)

        return self.func(function, *limits)

    def index(expr, x):
        """
        Return the index of a dummy variable in the list of limits.

        Usage
        =====

        ``index(expr, x)``  returns the index of the dummy variable ``x`` in the
        limits of ``expr``. Note that we start counting with 0 at the inner-most
        limits tuple.

        Examples
        ========

        >>> from sympy.abc import x, y, a, b, c, d
        >>> from sympy import Sum, Product
        >>> Sum(x*y, (x, a, b), (y, c, d)).index(x)
        0
        >>> Sum(x*y, (x, a, b), (y, c, d)).index(y)
        1
        >>> Product(x*y, (x, a, b), (y, c, d)).index(x)
        0
        >>> Product(x*y, (x, a, b), (y, c, d)).index(y)
        1

        See Also
        ========

        reorder_limit, reorder, reverse_order
        """
        variables = [limit[0] for limit in expr.limits]

        if variables.count(x) != 1:
            raise ValueError(expr, "Number of instances of variable not equal to one")
        else:
            return variables.index(x)

    def reorder(expr, *arg):
        """
        Reorder limits in a expression containing a Sum or a Product.

        Usage
        =====

        ``expr.reorder(*arg)`` reorders the limits in the expression ``expr``
        according to the list of tuples given by ``arg``. These tuples can
        contain numerical indices or index variable names or involve both.

        Examples
        ========

        >>> from sympy import Sum, Product
        >>> from sympy.abc import x, y, z, a, b, c, d, e, f

        >>> Sum(x*y, (x, a, b), (y, c, d)).reorder((x, y))
        Sum(x*y, (y, c, d), (x, a, b))

        >>> Sum(x*y*z, (x, a, b), (y, c, d), (z, e, f)).reorder((x, y), (x, z), (y, z))
        Sum(x*y*z, (z, e, f), (y, c, d), (x, a, b))

        >>> P = Product(x*y*z, (x, a, b), (y, c, d), (z, e, f))
        >>> P.reorder((x, y), (x, z), (y, z))
        Product(x*y*z, (z, e, f), (y, c, d), (x, a, b))

        We can also select the index variables by counting them, starting
        with the inner-most one:

        >>> Sum(x**2, (x, a, b), (x, c, d)).reorder((0, 1))
        Sum(x**2, (x, c, d), (x, a, b))

        And of course we can mix both schemes:

        >>> Sum(x*y, (x, a, b), (y, c, d)).reorder((y, x))
        Sum(x*y, (y, c, d), (x, a, b))
        >>> Sum(x*y, (x, a, b), (y, c, d)).reorder((y, 0))
        Sum(x*y, (y, c, d), (x, a, b))

        See Also
        ========

        reorder_limit, index, reverse_order
        """
        new_expr = expr

        for r in arg:
            if len(r) != 2:
                raise ValueError(r, "Invalid number of arguments")

            index1 = r[0]
            index2 = r[1]

            if not isinstance(r[0], int):
                index1 = expr.index(r[0])
            if not isinstance(r[1], int):
                index2 = expr.index(r[1])

            new_expr = new_expr.reorder_limit(index1, index2)

        return new_expr

    def reorder_limit(expr, x, y):
        """
        Interchange two limit tuples of a Sum or Product expression.

        Usage
        =====

        ``expr.reorder_limit(x, y)`` interchanges two limit tuples. The
        arguments ``x`` and ``y`` are integers corresponding to the index
        variables of the two limits which are to be interchanged. The
        expression ``expr`` has to be either a Sum or a Product.

        Examples
        ========

        >>> from sympy.abc import x, y, z, a, b, c, d, e, f
        >>> from sympy import Sum, Product

        >>> Sum(x*y*z, (x, a, b), (y, c, d), (z, e, f)).reorder_limit(0, 2)
        Sum(x*y*z, (z, e, f), (y, c, d), (x, a, b))
        >>> Sum(x**2, (x, a, b), (x, c, d)).reorder_limit(1, 0)
        Sum(x**2, (x, c, d), (x, a, b))

        >>> Product(x*y*z, (x, a, b), (y, c, d), (z, e, f)).reorder_limit(0, 2)
        Product(x*y*z, (z, e, f), (y, c, d), (x, a, b))

        See Also
        ========

        index, reorder, reverse_order
        """
        var = {limit[0] for limit in expr.limits}
        limit_x = expr.limits[x]
        limit_y = expr.limits[y]

        if (len(set(limit_x[1].free_symbols).intersection(var)) == 0 and
            len(set(limit_x[2].free_symbols).intersection(var)) == 0 and
            len(set(limit_y[1].free_symbols).intersection(var)) == 0 and
            len(set(limit_y[2].free_symbols).intersection(var)) == 0):

            limits = []
            for i, limit in enumerate(expr.limits):
                if i == x:
                    limits.append(limit_y)
                elif i == y:
                    limits.append(limit_x)
                else:
                    limits.append(limit)

            return type(expr)(expr.expr, *limits)
        else:
            raise ReorderError(expr, "could not interchange the two limits specified")

    def _latex(self, p):
        tex = '\\' + self.latex_name_of_operator
        if not self.limits:
            tex += ' '  
        elif len(self.limits) == 1:
            limit = self.limits[0]
            if len(limit) == 1:
                tex += r"_{%s} " % p._print(limit[0])
            elif len(limit) == 2:
                var, domain = limit
                if domain.is_bool:
#                     "\right." here is necessary to match the previous \left
                    tex += r"\limits_{%s \left| %s \right.}" % (var.latex, domain.latex)
                else:
                    tex += r"\limits_{\substack{%s \in %s}} " % tuple([p._print(i) for i in limit])                
            else:
                if limit[1].is_bool:
                    tex += r"\limits_{{%s \in %s} \left| %s \right.}" % (limit[0].latex, limit[2].latex, limit[1].latex)
                else:
                    x, a, b = limit
                    if a.is_Zero and x.is_integer and b.is_symbol:
                        tex += r"\limits_{%s:%s}" % tuple([p._print(s) for s in (x, b)])
                    else:
                        b -= 1
                        tex += r"\limits_{%s=%s}^{%s} " % tuple([p._print(i) for i in (x, a, b)])
        else:

            def _format_ineq(limit):
                if len(limit) == 1:
                    return p._print(limit[0])
                elif len(limit) == 2:
                    var, domain = limit
                    if domain.is_bool:
    #                     "\right." here is necessary to match the previous \left
                        return r"%s\left|%s\right." % tuple([p._print(i) for i in limit])
                    else:
                        return r"%s \in %s" % tuple([p._print(i) for i in limit])
                else:
                    x, a, b = limit
                    if b.is_set:
                        assert a.is_bool
                        return r"%s \in %s \left|%s\right." % (p._print(x), p._print(b), p._print(a))
                        
                    if x.is_integer:
                        if b.is_Add and b.args[0].is_One:
                            b -= 1
                            cmp = r"\leq"
                        else:
                            cmp = r"\lt"
                    else:
                        cmp = r"\leq"
                    return r"%s \leq %s %s %s" % (p._print(a), p._print(x), cmp, p._print(b))
                
            if all(len(limit) == 1 for limit in self.limits):
                tex += r"_{%s} " % str.join(', ', [p._print(l[0]) for l in self.limits])
            else:
                tex += r"\limits_{\substack{%s}} " % str.join('\\\\', [_format_ineq(l) for l in self.limits])

        if self.expr.is_Add:
            tex += r"\left(%s\right)" % p._print(self.expr)
        else:
            tex += p._print(self.expr)

        return tex
