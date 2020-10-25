import itertools

from sympy import (Expr, Add, Mul, S, Integral, Eq, Sum, Symbol,
                    expand as _expand, Not, Slice)
from sympy.core.compatibility import default_sort_key, ordered
from sympy.core.parameters import global_parameters
from sympy.core.sympify import _sympify
from sympy.core.relational import Relational, Equality, Unequal
from sympy.logic.boolalg import BooleanFunction, And
from sympy.stats import variance, covariance, rv
from sympy.stats.rv import (RandomSymbol, pspace, dependent,
                            given, sampling_E, RandomIndexedSymbol, is_random,
                            PSpace, sampling_P, random_symbols)
from sympy.concrete.expr_with_limits import ExprWithLimits, ForAll

__all__ = ['Probability', 'Expectation', 'Variance', 'Covariance']


@is_random.register(Expr)
def _(x):
    atoms = x.free_symbols
    if len(atoms) == 1 and next(iter(atoms)) == x:
        return False
    return any([is_random(i) for i in atoms])


@is_random.register(RandomSymbol)  # type: ignore
def _(x):
    return True


class Distributed(BooleanFunction):
    """
    Asserts that x is a random expression/symbol of the distribution S
    """

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq, *_ = args
            if eq.is_Equality:
                args = eq.args
                return self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs).simplify(), equivalent=[self, eq]).simplify()
            if isinstance(eq, dict):
                return self
            if eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)
        return BooleanFunction.subs(self, *args, **kwargs)

    def _latex(self, p):
        return r"%s \sim %s" % tuple(p._print(a) for a in self.args)

    def _sympystr(self, p):
        return r"%s ~ %s" % tuple(p._print(a) for a in self.args)

    @classmethod
    def eval(cls, x, s):
        if not s.is_distribution:
            raise TypeError('expecting Set, not %s' % s)

        ret = s.contains(x)
        if not isinstance(ret, Distributed) and (ret in (S.true, S.false) or ret.is_set):
            return ret

    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    def simplify(self, *_, **__):
        return self

    
class Conditioned(Expr):
    """
    Symbolic expression for the conditional randomal variables.
    """
    is_random = True
    
    lhs = property(lambda self: self.args[0])
    rhs = property(lambda self: self.args[1])
    
    def domain_defined(self, x):        
        return self.lhs.domain_defined(x) & self.rhs.domain_defined(x)            

    def simplify_condition_on_random_variable(self):
        condition = self.lhs.simplify_condition_on_random_variable()
        if condition is self.lhs:
            return self
        return self.func(condition, self.rhs)
    
    def __bool__(self):
        if self.is_boolean:
            return False
        return True

    def __new__(cls, prob, given):
        assert prob.is_random, prob
        assert given.is_random, given
        
        prob = _sympify(prob)
        given = _sympify(given)
        if prob.is_Conditioned:
            return Expr.__new__(cls, prob.lhs, prob.rhs & given)
        if prob.is_And:
            if given.is_And:
                if given._argset & prob._argset:
                    prob = prob.func(*prob._argset - given._argset)
            else:
                if given in prob._argset:
                    prob = prob.func(*prob._argset - {given})
        return Expr.__new__(cls, prob, given)

    def doit(self, **hints):
        return given(self.lhs, self.rhs)

    @property
    def atomic_dtype(self):        
        return self.lhs.atomic_dtype
    
    @property
    def shape(self):
        return self.lhs.shape
    
    def _latex(self, p):
        return r"%s \mid %s" % (p._print(self.lhs), p._print(self.rhs))

    def _eval_is_real(self):
        return self.lhs.is_real
    
    def _eval_is_complex(self):
        return self.lhs.is_complex

    def _eval_is_integer(self):
        return self.lhs.is_integer

    def _eval_is_finite(self):
        return self.lhs.is_finite

    def _eval_is_extended_negative(self):
        return self.lhs.is_extended_negative

    def _eval_is_extended_positive(self):
        return self.lhs.is_extended_positive

    @property
    def is_boolean(self):
        return self.lhs.is_boolean

    def domain_definition(self):
        return Unequal(Probability(self.rhs), 0)
        
    def invert(self):
        return self.func(self.lhs.invert(), self.rhs)
        
    def as_boolean(self):
        if not self.is_boolean:
            return self.func(self.lhs.as_boolean(), self.rhs)


# when X is a discrete random variable, define P(X) = P(X=x), which is necessarily nomore than 1         
# when X is a continuous random variable, define P(X) = PDF(X)(x) which is possibly greater than 1
class Probability(Expr):
    """
    Symbolic expression for the probability.

    Examples
    ========

    >>> from sympy.stats import Probability, Normal
    >>> from sympy import Integral
    >>> X = Normal("X", 0, 1)
    >>> prob = Probability(X > 1)
    >>> prob
    Probability(X > 1)

    Integral representation:

    >>> prob.rewrite(Integral)
    Integral(sqrt(2)*exp(-_z**2/2)/(2*sqrt(pi)), (_z, 1, oo))

    Evaluation of the integral:

    >>> prob.evaluate_integral()
    sqrt(2)*(-sqrt(2)*sqrt(pi)*erf(sqrt(2)/2) + sqrt(2)*sqrt(pi))/(4*sqrt(pi))
    """
    is_extended_negative = False
    is_extended_real = True
    is_finite = True
    
    def domain_defined(self, x):        
        return self.arg.domain_defined(x)            

    def marginalize(self, given):
        assert given.is_symbol and given.is_random        
        return self.func.marginalize_condition(self.arg, given)
                
    @classmethod    
    def marginalize_condition(cls, condition, given):        
        if condition.is_And:
            expr = []
            hit = False
            for eq in condition.args:
                if eq.is_Equality:
                    lhs, rhs = eq.args
                    if lhs.is_symbol and pspace(lhs).symbol == rhs:
                        if lhs._has(given):
                            if lhs == given:
                                hit = True
                                continue
                            
                            if given.is_Indexed:               
                                start = given.indices[0]
                                stop = start + 1
                            elif given.is_Slice:
                                start, stop = given.indices
                            else:
                                expr.append(eq)
                                continue                                                       
                                                                                                  
                            lhs = lhs.bisect(Slice[start:stop])
                            if not lhs.is_Concatenate:
                                hit = True
                            else:
                                rhs = rhs.bisect(Slice[start:stop])                                
                                for lhs, rhs in zip(lhs.args, rhs.args):
                                    eq = Equality(lhs, rhs)
                                    if lhs == given:
                                        hit = True
                                    else:
                                        expr.append(eq)
                            continue
                expr.append(eq)
            if hit:
                return cls(And(*expr))
        elif condition.is_Conditioned:
            self = cls(condition.lhs).marginalize(given)
            return self.func(self.arg, given=condition.rhs)
        elif condition.is_Equal:
            if given.is_Slice:
                start, stop = given.indices
                condition = condition.bisect(Slice[start:stop])
            elif given.is_Indexed:
                condition = condition.bisect(Slice[given.indices])
            if condition.is_And:
                return cls.marginalize_condition(condition, given)
            
    def total_probability_theorem(self, given):
        marginal_probability = self.marginalize(given)
        x = pspace(given).symbol
        if given.is_integer:
            return Equality(Sum[x](self), marginal_probability)
        else:
            return Equality(Integral[x](self), marginal_probability)
        
    def bayes_theorem(self, *given):
        if len(given) == 1:
            given = given[0]
            marginal_prob = self.marginalize(given)
        
            expr = marginal_prob.arg
            if expr.is_Conditioned and self.arg.is_Conditioned:
                given_probability = self.func(given, given=expr.rhs)
            else:
                given_probability = self.func(given)
            
            given_marginal_prob = self.func(expr, given=given)
            assert given_marginal_prob.arg.is_Conditioned
            
            if given_marginal_prob.arg.rhs.is_And:
                given_additions = given_marginal_prob.arg.rhs._argset - {given.as_boolean()}                    
                inequality = Unequal(self.func(given_probability.arg, given=And(*given_additions)), 0)
            else:
                inequality = Unequal(given_probability, 0)
            
            return ForAll[given: inequality](Equality(self, given_probability * given_marginal_prob))
        else:
            marginal_prob = self
            cond = S.true
            for g in given:
                marginal_prob = marginal_prob.marginalize(g)
                cond &= g.as_boolean()            
            
            expr = marginal_prob.arg
            if expr.is_Conditioned and self.arg.is_Conditioned:
                given_probability = self.func(cond, given=expr.rhs)
            else:
                given_probability = self.func(cond)
            
            given_marginal_prob = self.func(expr, given=cond)
            assert given_marginal_prob.arg.is_Conditioned
            
            if given_marginal_prob.arg.rhs.is_And:
                given_additions = given_marginal_prob.arg.rhs._argset - cond._argset                    
                inequality = Unequal(self.func(given_probability.arg, given=And(*given_additions)), 0)
            else:
                inequality = Unequal(given_probability, 0)
            
            return ForAll[given: inequality](Equality(self, given_probability * given_marginal_prob))

    @property
    def atomic_dtype(self):
        from sympy.core.symbol import dtype
        return dtype.real
    
    def __new__(cls, *prob, given=None): 
        booleans = []
        for arg in prob:
            assert arg.is_random
            if arg.is_symbol:
                booleans.append(Equality(arg, pspace(arg).symbol))
            elif arg.is_Conditioned:
                lhs, rhs = arg.args
                if lhs.is_symbol:
                    booleans.append(arg.func(Equality(lhs, pspace(lhs).symbol), rhs))
                else:
                    booleans.append(arg)
            else:
                assert arg.is_Boolean, type(arg)
                booleans.append(arg)
        expr = And(*booleans)
        if given is not None:
            expr = rv.given(expr, given)
        obj = Expr.__new__(cls, expr)
        return obj            

    def doit(self, **hints):
        condition = self.args[0]
        given_condition = self._condition
        numsamples = hints.get('numsamples', False)
        for_rewrite = not hints.get('for_rewrite', False)

        if isinstance(condition, Not):
            return S.One - self.func(condition.args[0], given_condition,
                                    evaluate=for_rewrite).doit(**hints)

        if condition.has(RandomIndexedSymbol):
            return pspace(condition).probability(condition, given_condition,
                                evaluate=for_rewrite)

        if isinstance(given_condition, RandomSymbol):
            condrv = random_symbols(condition)
            if len(condrv) == 1 and condrv[0] == given_condition:
                from sympy.stats.frv_types import BernoulliDistribution
                return BernoulliDistribution(self.func(condition).doit(**hints), 0, 1)
            if any([dependent(rv, given_condition) for rv in condrv]):
                return Probability(condition, given_condition)
            else:
                return Probability(condition).doit()

        if given_condition is not None and \
                not isinstance(given_condition, (Relational, Boolean)):
            raise ValueError("%s is not a relational or combination of relationals"
                    % (given_condition))

        if given_condition == False or condition is S.false:
            return S.Zero
        if not isinstance(condition, (Relational, Boolean)):
            raise ValueError("%s is not a relational or combination of relationals"
                    % (condition))
        if condition is S.true:
            return S.One

        if numsamples:
            return sampling_P(condition, given_condition, numsamples=numsamples)
        if given_condition is not None:  # If there is a condition
            # Recompute on new conditional expr
            return Probability(given(condition, given_condition)).doit()

        # Otherwise pass work off to the ProbabilitySpace
        if pspace(condition) == PSpace():
            return Probability(condition, given_condition)

        result = pspace(condition).probability(condition)
        if hasattr(result, 'doit') and for_rewrite:
            return result.doit()
        else:
            return result

    def _eval_rewrite_as_Integral(self, arg, condition=None, **kwargs):
        return self.func(arg, condition=condition).doit(for_rewrite=True)

    _eval_rewrite_as_Sum = _eval_rewrite_as_Integral

    def evaluate_integral(self):
        return self.rewrite(Integral).doit()

    def _latex(self, p):        
        return r'\mathbb{P}%s' % p._print(self.args)
    
    def domain_definition(self):        
        return self.arg.domain_definition()
    
    def _subs(self, old, new, **hints):
        if old.is_Conditioned and not old.lhs.is_boolean or new.is_Conditioned and not new.lhs.is_boolean:
            old = old.as_boolean()
            new = new.as_boolean()
        return Expr._subs(self, old, new, **hints)

    
class Expectation(ExprWithLimits):
    """
    Symbolic expression for the expectation.

    Examples
    ========

    >>> from sympy.stats import Expectation, Normal, Probability, Poisson
    >>> from sympy import symbols, Integral, Sum
    >>> mu = symbols("mu")
    >>> sigma = symbols("sigma", positive=True)
    >>> X = Normal("X", mu, sigma)
    >>> Expectation(X)
    Expectation(X)
    >>> Expectation(X).evaluate_integral().simplify()
    mu

    To get the integral expression of the expectation:

    >>> Expectation(X).rewrite(Integral)
    Integral(sqrt(2)*X*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo))

    The same integral expression, in more abstract terms:

    >>> Expectation(X).rewrite(Probability)
    Integral(x*Probability(Eq(X, x)), (x, -oo, oo))

    To get the Summation expression of the expectation for discrete random variables:

    >>> lamda = symbols('lamda', positive=True)
    >>> Z = Poisson('Z', lamda)
    >>> Expectation(Z).rewrite(Sum)
    Sum(Z*lamda**Z*exp(-lamda)/factorial(Z), (Z, 0, oo))

    This class is aware of some properties of the expectation:

    >>> from sympy.abc import a
    >>> Expectation(a*X)
    Expectation(a*X)
    >>> Y = Normal("Y", 1, 2)
    >>> Expectation(X + Y)
    Expectation(X + Y)

    To expand the ``Expectation`` into its expression, use ``expand()``:

    >>> Expectation(X + Y).expand()
    Expectation(X) + Expectation(Y)
    >>> Expectation(a*X + Y).expand()
    a*Expectation(X) + Expectation(Y)
    >>> Expectation(a*X + Y)
    Expectation(a*X + Y)
    >>> Expectation((X + Y)*(X - Y)).expand()
    Expectation(X**2) - Expectation(Y**2)

    To evaluate the ``Expectation``, use ``doit()``:

    >>> Expectation(X + Y).doit()
    mu + 1
    >>> Expectation(X + Expectation(Y + Expectation(2*X))).doit()
    3*mu + 1

    To prevent evaluating nested ``Expectation``, use ``doit(deep=False)``

    >>> Expectation(X + Expectation(Y)).doit(deep=False)
    mu + Expectation(Expectation(Y))
    >>> Expectation(X + Expectation(Y + Expectation(2*X))).doit(deep=False)
    mu + Expectation(Expectation(Y + Expectation(2*X)))

    """
    is_Expectation = True
    is_complex = True
    
    def __new__(cls, expr, *limits, **kwargs):
        expr = _sympify(expr)
        if expr.is_Matrix:
            from sympy.stats.symbolic_multivariate_probability import ExpectationMatrix
            return ExpectationMatrix(expr)
        if not expr.is_random:
            return expr
        return ExprWithLimits.__new__(cls, expr, *limits)
    
    @property
    def expr(self):
        return self.args[0]

    @property
    def atomic_dtype(self):
        return self.expr.atomic_dtype

    @property
    def shape(self):
        return self.expr.shape

    def expand(self, **hints):
        expr = self.args[0]
        condition = self._condition

        if not is_random(expr):
            return expr

        if isinstance(expr, Add):
            return Add.fromiter(Expectation(a, condition=condition).expand()
                    for a in expr.args)

        expand_expr = _expand(expr)
        if isinstance(expand_expr, Add):
            return Add.fromiter(Expectation(a, condition=condition).expand()
                    for a in expand_expr.args)

        elif isinstance(expr, Mul):
            rv = []
            nonrv = []
            for a in expr.args:
                if is_random(a):
                    rv.append(a)
                else:
                    nonrv.append(a)
            return Mul.fromiter(nonrv) * Expectation(Mul.fromiter(rv), condition=condition)

        return self

    def doit(self, **hints):
        if self.limits:
            function = self.function
            for limit in self.limits:
                x, distribution = limit                
                _x = x.copy(distribution=distribution)
                expr = function._subs(x, _x)
                if expr.is_Conditioned:
                    expr = expr.doit()                    
                if not expr.is_random:  # expr isn't random?
                    return expr
                ps = pspace(expr)
                if ps == PSpace():
                    return self.func(expr)
                # Otherwise case is simple, pass work off to the ProbabilitySpace
                function = ps.compute_expectation(expr, evaluate=True)
                if hasattr(function, 'doit'):
                    function = function.doit(**hints)
            return function
        else:
            deep = hints.get('deep', True)
            expr = self.args[0]
            numsamples = hints.get('numsamples', False)
            for_rewrite = not hints.get('for_rewrite', False)
    
            if deep:
                expr = expr.doit(**hints)
    
            if not expr.is_random or isinstance(expr, Expectation):  # expr isn't random?
                return expr
            if numsamples:  # Computing by monte carlo sampling?
                evalf = hints.get('evalf', True)
                return sampling_E(expr, numsamples=numsamples, evalf=evalf)
    
            if expr.has(RandomIndexedSymbol):
                return pspace(expr).compute_expectation(expr)
    
            # A few known statements for efficiency
    
            if expr.is_Add:  # We know that E is Linear
                return Add(*[self.func(arg).doit(**hints)
                        if not isinstance(arg, Expectation) else self.func(arg)
                             for arg in expr.args])
            if expr.is_Mul:
                if expr.atoms(Expectation):
                    return expr
    
            ps = pspace(expr)
            if ps == PSpace():
                return self.func(expr)
            # Otherwise case is simple, pass work off to the ProbabilitySpace
            result = ps.compute_expectation(expr, evaluate=for_rewrite)
            if hasattr(result, 'doit') and for_rewrite:
                return result.doit(**hints)
            else:
                return result

    def _eval_rewrite_as_Probability(self, arg, condition=None, **kwargs):
        rvs = arg.atoms(RandomSymbol)
        if len(rvs) > 1:
            raise NotImplementedError()
        if len(rvs) == 0:
            return arg

        rv = rvs.pop()
        if rv.pspace is None:
            raise ValueError("Probability space not known")

        symbol = rv.symbol
        if symbol.name[0].isupper():
            symbol = Symbol(symbol.name.lower())
        else :
            symbol = Symbol(symbol.name + "_1")

        if rv.pspace.is_Continuous:
            return Integral(arg.replace(rv, symbol) * Probability(Eq(rv, symbol), condition), (symbol, rv.pspace.domain.set.inf, rv.pspace.domain.set.sup))
        else:
            if rv.pspace.is_Finite:
                raise NotImplementedError
            else:
                return Sum(arg.replace(rv, symbol) * Probability(Eq(rv, symbol), condition), (symbol, rv.pspace.domain.set.inf, rv.pspace.set.sup))

    def _eval_rewrite_as_Integral(self, arg, condition=None, **kwargs):
        return self.func(arg, condition=condition).doit(deep=False, for_rewrite=True)

    _eval_rewrite_as_Sum = _eval_rewrite_as_Integral  # For discrete this will be Sum

    def evaluate_integral(self):
        return self.rewrite(Integral).doit()

    evaluate_sum = evaluate_integral

    def _latex(self, p):
        tex = r'\mathop{\mathbb{E}}'
        limits = self.limits
        if not limits:
            tex += ' '  
        elif len(limits) == 1:
            limit = limits[0]
            if len(limit) == 1:
                tex += r"_{%s} " % p._print(limit[0])
            else:
                tex += r"\limits_{%s \sim %s} " % tuple([p._print(i) for i in limit])
        else:

            def _format_ineq(limit):
                if len(limit) == 1:
                    return p._print(limit[0])
                else:
                    return r"%s \sim %s" % tuple([p._print(i) for i in limit])

            if all(len(limit) == 1 for limit in limits):
                tex += r"_{%s} " % str.join(', ', [p._print(l[0]) for l in limits])
            else:
                tex += r"\limits_{\begin{subarray}{c}%s\end{subarray}} " % str.join('\\\\', [_format_ineq(l) for l in limits])

        if self.function.is_Add or self.function.is_Conditioned:
            tex += r"\left(%s\right)" % p._print(self.function)
        else:
            tex += p._print(self.function)

        return tex


class Variance(Expr):
    """
    Symbolic expression for the variance.

    Examples
    ========

    >>> from sympy import symbols, Integral
    >>> from sympy.stats import Normal, Expectation, Variance, Probability
    >>> mu = symbols("mu", positive=True)
    >>> sigma = symbols("sigma", positive=True)
    >>> X = Normal("X", mu, sigma)
    >>> Variance(X)
    Variance(X)
    >>> Variance(X).evaluate_integral()
    sigma**2

    Integral representation of the underlying calculations:

    >>> Variance(X).rewrite(Integral)
    Integral(sqrt(2)*(X - Integral(sqrt(2)*X*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo)))**2*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo))

    Integral representation, without expanding the PDF:

    >>> Variance(X).rewrite(Probability)
    -Integral(x*Probability(Eq(X, x)), (x, -oo, oo))**2 + Integral(x**2*Probability(Eq(X, x)), (x, -oo, oo))

    Rewrite the variance in terms of the expectation

    >>> Variance(X).rewrite(Expectation)
    -Expectation(X)**2 + Expectation(X**2)

    Some transformations based on the properties of the variance may happen:

    >>> from sympy.abc import a
    >>> Y = Normal("Y", 0, 1)
    >>> Variance(a*X)
    Variance(a*X)

    To expand the variance in its expression, use ``expand()``:

    >>> Variance(a*X).expand()
    a**2*Variance(X)
    >>> Variance(X + Y)
    Variance(X + Y)
    >>> Variance(X + Y).expand()
    2*Covariance(X, Y) + Variance(X) + Variance(Y)

    """

    def __new__(cls, arg, condition=None, **kwargs):
        arg = _sympify(arg)

        if arg.is_Matrix:
            from sympy.stats.symbolic_multivariate_probability import VarianceMatrix
            return VarianceMatrix(arg, condition)
        if condition is None:
            obj = Expr.__new__(cls, arg)
        else:
            condition = _sympify(condition)
            obj = Expr.__new__(cls, arg, condition)
        obj._condition = condition
        return obj

    def expand(self, **hints):
        arg = self.args[0]
        condition = self._condition

        if not is_random(arg):
            return S.Zero

        if isinstance(arg, RandomSymbol):
            return self
        elif isinstance(arg, Add):
            rv = []
            for a in arg.args:
                if is_random(a):
                    rv.append(a)
            variances = Add(*map(lambda xv: Variance(xv, condition).expand(), rv))
            map_to_covar = lambda x: 2 * Covariance(*x, condition=condition).expand()
            covariances = Add(*map(map_to_covar, itertools.combinations(rv, 2)))
            return variances + covariances
        elif isinstance(arg, Mul):
            nonrv = []
            rv = []
            for a in arg.args:
                if is_random(a):
                    rv.append(a)
                else:
                    nonrv.append(a ** 2)
            if len(rv) == 0:
                return S.Zero
            return Mul.fromiter(nonrv) * Variance(Mul.fromiter(rv), condition)

        # this expression contains a RandomSymbol somehow:
        return self

    def _eval_rewrite_as_Expectation(self, arg, condition=None, **kwargs):
            e1 = Expectation(arg ** 2, condition)
            e2 = Expectation(arg, condition) ** 2
            return e1 - e2

    def _eval_rewrite_as_Probability(self, arg, condition=None, **kwargs):
        return self.rewrite(Expectation).rewrite(Probability)

    def _eval_rewrite_as_Integral(self, arg, condition=None, **kwargs):
        return variance(self.args[0], self._condition, evaluate=False)

    _eval_rewrite_as_Sum = _eval_rewrite_as_Integral

    def evaluate_integral(self):
        return self.rewrite(Integral).doit()


class Covariance(Expr):
    """
    Symbolic expression for the covariance.

    Examples
    ========

    >>> from sympy.stats import Covariance
    >>> from sympy.stats import Normal
    >>> X = Normal("X", 3, 2)
    >>> Y = Normal("Y", 0, 1)
    >>> Z = Normal("Z", 0, 1)
    >>> W = Normal("W", 0, 1)
    >>> cexpr = Covariance(X, Y)
    >>> cexpr
    Covariance(X, Y)

    Evaluate the covariance, `X` and `Y` are independent,
    therefore zero is the result:

    >>> cexpr.evaluate_integral()
    0

    Rewrite the covariance expression in terms of expectations:

    >>> from sympy.stats import Expectation
    >>> cexpr.rewrite(Expectation)
    Expectation(X*Y) - Expectation(X)*Expectation(Y)

    In order to expand the argument, use ``expand()``:

    >>> from sympy.abc import a, b, c, d
    >>> Covariance(a*X + b*Y, c*Z + d*W)
    Covariance(a*X + b*Y, c*Z + d*W)
    >>> Covariance(a*X + b*Y, c*Z + d*W).expand()
    a*c*Covariance(X, Z) + a*d*Covariance(W, X) + b*c*Covariance(Y, Z) + b*d*Covariance(W, Y)

    This class is aware of some properties of the covariance:

    >>> Covariance(X, X).expand()
    Variance(X)
    >>> Covariance(a*X, b*Y).expand()
    a*b*Covariance(X, Y)
    """

    def __new__(cls, arg1, arg2, condition=None, **kwargs):
        arg1 = _sympify(arg1)
        arg2 = _sympify(arg2)

        if arg1.is_Matrix or arg2.is_Matrix:
            from sympy.stats.symbolic_multivariate_probability import CrossCovarianceMatrix
            return CrossCovarianceMatrix(arg1, arg2, condition)

        if kwargs.pop('evaluate', global_parameters.evaluate):
            arg1, arg2 = sorted([arg1, arg2], key=default_sort_key)

        if condition is None:
            obj = Expr.__new__(cls, arg1, arg2)
        else:
            condition = _sympify(condition)
            obj = Expr.__new__(cls, arg1, arg2, condition)
        obj._condition = condition
        return obj

    def expand(self, **hints):
        arg1 = self.args[0]
        arg2 = self.args[1]
        condition = self._condition

        if arg1 == arg2:
            return Variance(arg1, condition).expand()

        if not is_random(arg1):
            return S.Zero
        if not is_random(arg2):
            return S.Zero

        arg1, arg2 = sorted([arg1, arg2], key=default_sort_key)

        if isinstance(arg1, RandomSymbol) and isinstance(arg2, RandomSymbol):
            return Covariance(arg1, arg2, condition)

        coeff_rv_list1 = self._expand_single_argument(arg1.expand())
        coeff_rv_list2 = self._expand_single_argument(arg2.expand())

        addends = [a * b * Covariance(*sorted([r1, r2], key=default_sort_key), condition=condition)
                   for (a, r1) in coeff_rv_list1 for (b, r2) in coeff_rv_list2]
        return Add.fromiter(addends)

    @classmethod
    def _expand_single_argument(cls, expr):
        # return (coefficient, random_symbol) pairs:
        if isinstance(expr, RandomSymbol):
            return [(S.One, expr)]
        elif isinstance(expr, Add):
            outval = []
            for a in expr.args:
                if isinstance(a, Mul):
                    outval.append(cls._get_mul_nonrv_rv_tuple(a))
                elif is_random(a):
                    outval.append((S.One, a))

            return outval
        elif isinstance(expr, Mul):
            return [cls._get_mul_nonrv_rv_tuple(expr)]
        elif is_random(expr):
            return [(S.One, expr)]

    @classmethod
    def _get_mul_nonrv_rv_tuple(cls, m):
        rv = []
        nonrv = []
        for a in m.args:
            if is_random(a):
                rv.append(a)
            else:
                nonrv.append(a)
        return (Mul.fromiter(nonrv), Mul.fromiter(rv))

    def _eval_rewrite_as_Expectation(self, arg1, arg2, condition=None, **kwargs):
        e1 = Expectation(arg1 * arg2, condition)
        e2 = Expectation(arg1, condition) * Expectation(arg2, condition)
        return e1 - e2

    def _eval_rewrite_as_Probability(self, arg1, arg2, condition=None, **kwargs):
        return self.rewrite(Expectation).rewrite(Probability)

    def _eval_rewrite_as_Integral(self, arg1, arg2, condition=None, **kwargs):
        return covariance(self.args[0], self.args[1], self._condition, evaluate=False)

    _eval_rewrite_as_Sum = _eval_rewrite_as_Integral

    def evaluate_integral(self):
        return self.rewrite(Integral).doit()


class Moment(Expr):
    """
    Symbolic class for Moment

    Examples
    ========

    >>> from sympy import Symbol, Integral
    >>> from sympy.stats import Normal, Expectation, Probability, Moment
    >>> mu = Symbol('mu', real=True)
    >>> sigma = Symbol('sigma', real=True, positive=True)
    >>> X = Normal('X', mu, sigma)
    >>> M = Moment(X, 3, 1)

    To evaluate the result of Moment use `doit`:

    >>> M.doit()
    mu**3 - 3*mu**2 + 3*mu*sigma**2 + 3*mu - 3*sigma**2 - 1

    Rewrite the Moment expression in terms of Expectation:

    >>> M.rewrite(Expectation)
    Expectation((X - 1)**3)

    Rewrite the Moment expression in terms of Probability:

    >>> M.rewrite(Probability)
    Integral((x - 1)**3*Probability(Eq(X, x)), (x, -oo, oo))

    Rewrite the Moment expression in terms of Integral:

    >>> M.rewrite(Integral)
    Integral(sqrt(2)*(X - 1)**3*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo))

    """

    def __new__(cls, X, n, c=0, condition=None, **kwargs):
        X = _sympify(X)
        n = _sympify(n)
        c = _sympify(c)
        if condition is not None:
            condition = _sympify(condition)
        return Expr.__new__(cls, X, n, c, condition)

    def doit(self, **hints):
        if not is_random(self.args[0]):
            return self.args[0]
        return self.rewrite(Expectation).doit(**hints)

    def _eval_rewrite_as_Expectation(self, X, n, c=0, condition=None, **kwargs):
        return Expectation((X - c) ** n, condition)

    def _eval_rewrite_as_Probability(self, X, n, c=0, condition=None, **kwargs):
        return self.rewrite(Expectation).rewrite(Probability)

    def _eval_rewrite_as_Integral(self, X, n, c=0, condition=None, **kwargs):
        return self.rewrite(Expectation).rewrite(Integral)


class CentralMoment(Expr):
    """
    Symbolic class Central Moment

    Examples
    ========

    >>> from sympy import Symbol, Integral
    >>> from sympy.stats import Normal, Expectation, Probability, CentralMoment
    >>> mu = Symbol('mu', real=True)
    >>> sigma = Symbol('sigma', real=True, positive=True)
    >>> X = Normal('X', mu, sigma)
    >>> CM = CentralMoment(X, 4)

    To evaluate the result of CentralMoment use `doit`:

    >>> CM.doit().simplify()
    3*sigma**4

    Rewrite the CentralMoment expression in terms of Expectation:

    >>> CM.rewrite(Expectation)
    Expectation((X - Expectation(X))**4)

    Rewrite the CentralMoment expression in terms of Probability:

    >>> CM.rewrite(Probability)
    Integral((x - Integral(x*Probability(True), (x, -oo, oo)))**4*Probability(Eq(X, x)), (x, -oo, oo))

    Rewrite the CentralMoment expression in terms of Integral:

    >>> CM.rewrite(Integral)
    Integral(sqrt(2)*(X - Integral(sqrt(2)*X*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo)))**4*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo))

    """

    def __new__(cls, X, n, condition=None, **kwargs):
        X = _sympify(X)
        n = _sympify(n)
        if condition is not None:
            condition = _sympify(condition)
        return Expr.__new__(cls, X, n, condition)

    def doit(self, **hints):
        if not is_random(self.args[0]):
            return self.args[0]
        return self.rewrite(Expectation).doit(**hints)

    def _eval_rewrite_as_Expectation(self, X, n, condition=None, **kwargs):
        mu = Expectation(X, condition, **kwargs)
        return Moment(X, n, mu, condition, **kwargs).rewrite(Expectation)

    def _eval_rewrite_as_Probability(self, X, n, condition=None, **kwargs):
        return self.rewrite(Expectation).rewrite(Probability)

    def _eval_rewrite_as_Integral(self, X, n, condition=None, **kwargs):
        return self.rewrite(Expectation).rewrite(Integral)
