"""
Main Random Variables Module

Defines abstract random variable type.
Contains interfaces for probability space object (PSpace) as well as standard
operators, P, E, sample, density, where, quantile

See Also
========

sympy.stats.crv
sympy.stats.frv
sympy.stats.rv_interface
"""

from functools import singledispatch
from typing import Tuple as tTuple

from sympy import (Basic, S, Expr, Symbol, Tuple, And, Add, Eq, lambdify, Or,
                   Equal, Lambda, sympify, Dummy, Ne, KroneckerDelta,
                   DiracDelta, Mul, Indexed, MatrixSymbol, Function)
from sympy.core.relational import Relational
from sympy.core.sympify import _sympify
from sympy.sets.sets import FiniteSet, ProductSet, Intersection
from sympy.solvers.solveset import solveset
from sympy.external import import_module
from sympy.utilities.miscellany import filldedent
import warnings
from sympy.core.symbol import dtype
from sympy.matrices.expressions.blockmatrix import BlockMatrix
# x = Symbol('x')


@singledispatch
def is_random(x):
    return False


@is_random.register(Basic)
def _(x):
    atoms = x.free_symbols
    return any([is_random(i) for i in atoms])


class RandomDomain(Basic):
    """
    Represents a set of variables and the values which they can take

    See Also
    ========

    sympy.stats.crv.ContinuousDomain
    sympy.stats.frv.FiniteDomain
    """

    is_ProductDomain = False
    is_Finite = False
    is_Continuous = False
    is_Discrete = False

    def __new__(cls, symbols, *args):
        symbols = FiniteSet(*symbols)
        return Basic.__new__(cls, symbols, *args)

    @property
    def symbols(self):
        return self.args[0]

    @property
    def set(self):
        return self.args[1]

    def __contains__(self, other):
        raise NotImplementedError()

    def compute_expectation(self, expr):
        raise NotImplementedError()


class SingleDomain(RandomDomain):
    """
    A single variable and its domain

    See Also
    ========

    sympy.stats.crv.SingleContinuousDomain
    sympy.stats.frv.SingleFiniteDomain
    """

    def __new__(cls, symbol, set):        
        assert symbol.is_Symbol or symbol.is_Indexed
        return Basic.__new__(cls, symbol, set)

    @property
    def symbol(self):
        return self.args[0]

    @property
    def symbols(self):
        return FiniteSet(self.symbol)

    def __contains__(self, other):
        if len(other) != 1:
            return False
        sym, val = tuple(other)[0]
        return self.symbol == sym and val in self.set


class MatrixDomain(RandomDomain):
    """
    A Random Matrix variable and its domain

    """

    def __new__(cls, symbol, set):
        symbol, set = _symbol_converter(symbol), _sympify(set)
        return Basic.__new__(cls, symbol, set)

    @property
    def symbol(self):
        return self.args[0]

    @property
    def symbols(self):
        return FiniteSet(self.symbol)


class ConditionalDomain(RandomDomain):
    """
    A RandomDomain with an attached condition

    See Also
    ========

    sympy.stats.crv.ConditionalContinuousDomain
    sympy.stats.frv.ConditionalFiniteDomain
    """

    def __new__(cls, fulldomain, condition):
#         condition = condition.xreplace({rs: rs.symbol
#             for rs in random_symbols(condition)})
        return Basic.__new__(cls, fulldomain, condition)

    @property
    def symbols(self):
        return self.fulldomain.symbols

    @property
    def symbol(self):
        return self.fulldomain.symbol
    
    @property
    def fulldomain(self):
        return self.args[0]

    @property
    def condition(self):
        return self.args[1]

    @property
    def set(self):
        raise NotImplementedError("Set of Conditional Domain not Implemented")

    def as_boolean(self):
        return And(self.fulldomain.as_boolean(), self.condition)


class PSpace(Basic):
    """
    A Probability Space

    Probability Spaces encode processes that equal different values
    probabilistically. These underly Random Symbols which occur in SymPy
    expressions and contain the mechanics to evaluate statistical statements.

    See Also
    ========

    sympy.stats.crv.ContinuousPSpace
    sympy.stats.frv.FinitePSpace
    """

    is_Finite = None  # type: bool
    is_Continuous = None  # type: bool
    is_Discrete = None  # type: bool
    is_real = None  # type: bool

#     @property
#     def domain(self):
#         return self.args[0]

    @property
    def density(self):
        return self.args[1]

#     @property
#     def symbols(self):
#         return self.domain.symbols

#     @property
#     def symbol(self):
#         return self.domain.symbol

    def where(self, condition):
        raise NotImplementedError()

    def compute_density(self, expr):
        raise NotImplementedError()

    def sample(self):
        raise NotImplementedError()

    def probability(self, condition):
        raise NotImplementedError()

    def compute_expectation(self, expr):
        raise NotImplementedError()


class SinglePSpace(PSpace):
    """
    Represents the probabilities of a set of random events that can be
    attributed to a single variable/symbol.
    """

    def __new__(cls, symbol, distribution=None):
        if distribution is None:
            value = symbol
            if value.shape:
                symbol = value.copy(domain=value.domain_assumed, random=None)
            else:
                symbol = value.copy(nonnegative=value.is_nonnegative, domain=value.domain, random=None)
            distribution = value.distribution
        else:
            if isinstance(symbol, str):
                if distribution.set in S.Naturals0:
                    symbol = Symbol(symbol, integer=True, domain=distribution.set)
                elif distribution.set == S.Integers:
                    symbol = Symbol(symbol, integer=True)
                elif distribution.set.is_extended_nonnegative:
                    symbol = Symbol(symbol, real=True, nonnegative=True)
                else:
                    symbol = Symbol(symbol, real=True)
            if not isinstance(symbol, (Symbol, Indexed)):
                raise TypeError("symbol should have been string or Symbol")
    
            assumptions = symbol.assumptions0
            if symbol.is_Indexed:
                from sympy import LAMBDA
                distribution = LAMBDA(distribution, *((i,) for i in symbol.indices))
                value = symbol.base.copy(distribution=distribution, **assumptions)[symbol.indices]
            else:
                value = symbol.copy(distribution=distribution, **assumptions)

        return Basic.__new__(cls, symbol, distribution, value)

    @property
    def symbol(self):
        return self.args[0]

    @property
    def symbols(self):
        return {self.symbol}

    @property
    def distribution(self):
        return self.args[1]

    @property
    def pdf(self):
        return self.distribution.pdf(self.symbol)


class RandomSymbol(Expr):
    """
    Random Symbols represent ProbabilitySpaces in SymPy Expressions
    In principle they can take on any value that their symbol can take on
    within the associated PSpace with probability determined by the PSpace
    Density.

    Random Symbols contain pspace and symbol properties.
    The pspace property points to the represented Probability Space
    The symbol is a standard SymPy Symbol that is used in that probability space
    for example in defining a density.

    You can form normal SymPy expressions using RandomSymbols and operate on
    those expressions with the Functions

    E - Expectation of a random expression
    P - Probability of a condition
    density - Probability Density of an expression
    given - A new random expression (with new random symbols) given a condition

    An object of the RandomSymbol type should almost never be created by the
    user. They tend to be created instead by the PSpace class's value method.
    Traditionally a user doesn't even do this but instead calls one of the
    convenience functions Normal, Exponential, Coin, Die, FiniteRV, etc....
    """

    @property
    def dtype(self):
        return self.symbol.dtype

    @property
    def shape(self):
        return self.symbol.shape

    def __new__(cls, symbol, pspace=None):
        from sympy.stats.joint_rv import JointRandomSymbol
        if pspace is None:
            # Allow single arg, representing pspace == PSpace()
            pspace = PSpace()
        symbol = _symbol_converter(symbol)
        if not isinstance(pspace, PSpace):
            raise TypeError("pspace variable should be of type PSpace")
        if cls == JointRandomSymbol and isinstance(pspace, SinglePSpace):
            cls = RandomSymbol
        return Basic.__new__(cls, symbol, pspace)

    is_finite = True
    is_symbol = True
    is_Atom = True

    _diff_wrt = True

    pspace = property(lambda self: self.args[1])
    symbol = property(lambda self: self.args[0])
    name = property(lambda self: self.symbol.name)

    def _eval_is_extended_positive(self):
        return self.symbol.is_extended_positive

    def _eval_is_integer(self):
        return self.symbol.is_integer

    def _eval_is_extended_real(self):
        return self.symbol.is_extended_real or self.pspace.is_extended_real

    @property
    def is_commutative(self):
        return self.symbol.is_commutative

    @property
    def free_symbols(self):
        s = {self}
        if self.symbol.is_Indexed:
            for index in self.symbol.indices:
                s |= index.free_symbols
        return s

    @property
    def domain(self):
        return self.symbol.domain

    def _sympystr(self, _):   
        return Symbol.sympystr(self.name)

    def _latex(self, p, style='plain'):
        return r'{\color{red} {\mathbf{%s}}}' % p._print(self.symbol.copy())


class RandomIndexedSymbol(RandomSymbol):

    def __new__(cls, idx_obj, pspace=None):
        if pspace is None:
            # Allow single arg, representing pspace == PSpace()
            pspace = PSpace()
        if not isinstance(idx_obj, (Indexed, Function)):
            raise TypeError("An Function or Indexed object is expected not %s" % (idx_obj))
        return Basic.__new__(cls, idx_obj, pspace)

    symbol = property(lambda self: self.args[0])
    name = property(lambda self: str(self.args[0]))

    @property
    def key(self):
        if isinstance(self.symbol, Indexed):
            return self.symbol.args[1]
        elif isinstance(self.symbol, Function):
            return self.symbol.args[0]

    @property
    def free_symbols(self):
        if self.key.free_symbols:
            free_syms = self.key.free_symbols
            free_syms.add(self)
            return free_syms
        return {self}


class RandomMatrixSymbol(RandomSymbol, MatrixSymbol):  # type: ignore

    def __new__(cls, symbol, n, m, pspace=None):
        n, m = _sympify(n), _sympify(m)
        symbol = _symbol_converter(symbol)
        if pspace is None:
            # Allow single arg, representing pspace == PSpace()
            pspace = PSpace()
        return Basic.__new__(cls, symbol, n, m, pspace)

    symbol = property(lambda self: self.args[0])
    pspace = property(lambda self: self.args[3])


class ProductPSpace(PSpace):
    """
    Abstract class for representing probability spaces with multiple random
    variables.

    See Also
    ========

    sympy.stats.rv.IndependentProductPSpace
    sympy.stats.joint_rv.JointPSpace
    """
    pass


class IndependentProductPSpace(ProductPSpace):
    """
    A probability space resulting from the merger of two independent probability
    spaces.

    Often created using the function, pspace
    """

    def __new__(cls, *spaces):
#         rs_space_dict = {}
#         for space in spaces:
#             for value in space.values:
#                 rs_space_dict[value] = space

        symbols = set().union(*[sp.symbols for sp in spaces])

        # Overlapping symbols
        from sympy.stats.joint_rv import MarginalDistribution
        from sympy.stats.compound_rv import CompoundDistribution
        if len(symbols) < sum(len(space.symbols) for space in spaces if not
         isinstance(space.distribution, (
            CompoundDistribution, MarginalDistribution))):
            raise ValueError("Overlapping Random Variables")

        if all(space.is_Finite for space in spaces):
            from sympy.stats.frv import ProductFinitePSpace
            cls = ProductFinitePSpace

        obj = Basic.__new__(cls, *FiniteSet(*spaces))

        return obj

    @property
    def pdf(self):
        p = Mul(*[space.pdf for space in self.spaces])
        return p.subs({rv: rv.symbol for rv in self.values})

    @property
    def rs_space_dict(self):
        d = {}
        for space in self.spaces:
            for value in space.values:
                d[value] = space
        return d

    @property
    def symbols(self):
        return FiniteSet(*[val.symbol for val in self.rs_space_dict.keys()])

    @property
    def spaces(self):
        return FiniteSet(*self.args)

    def values2symbols(self):
        return {space.value : space.symbol for space in self.args}

    @property
    def values(self):
        return sumsets(space.values for space in self.spaces)

    def compute_expectation(self, expr, rvs=None, evaluate=False, **kwargs):
        rvs = rvs or self.values
        rvs = frozenset(rvs)
        for space in self.spaces:
            expr = space.compute_expectation(expr, rvs & space.values, evaluate=False, **kwargs)
        if evaluate and hasattr(expr, 'doit'):
            return expr.doit(**kwargs)
        return expr

    @property
    def domain(self):
        return ProductDomain(*[space.domain for space in self.spaces])

    @property
    def density(self):
        raise NotImplementedError("Density not available for ProductSpaces")

    def sample(self, size=(), library='scipy'):
        return {k: v for space in self.spaces
            for k, v in space.sample(size=size, library=library).items()}

    def probability(self, condition, **kwargs):
        cond_inv = False
        if isinstance(condition, Ne):
            condition = Eq(condition.args[0], condition.args[1])
            cond_inv = True
        elif isinstance(condition, And):  # they are independent
            return Mul(*[self.probability(arg) for arg in condition.args])
        elif isinstance(condition, Or):  # they are independent
            return Add(*[self.probability(arg) for arg in condition.args])
        expr = condition.lhs - condition.rhs
        rvs = random_symbols(expr)
        dens = self.compute_density(expr)
        if any([pspace(rv).is_Continuous for rv in rvs]):
            from sympy.stats.crv import SingleContinuousPSpace
            from sympy.stats.crv_types import ContinuousDistributionHandmade
            if expr in self.values:
                # Marginalize all other random symbols out of the density
                randomsymbols = tuple(set(self.values) - frozenset([expr]))
                symbols = tuple(rs.symbol for rs in randomsymbols)
                pdf = self.domain.integrate(self.pdf, symbols, **kwargs)
                return Lambda(expr.symbol, pdf)
            dens = ContinuousDistributionHandmade(dens)
            z = Dummy('z', real=True)
            space = SingleContinuousPSpace(z, dens)
            result = space.probability(condition.__class__(space.value, 0))
        else:
            from sympy.stats.drv import SingleDiscretePSpace
            from sympy.stats.drv_types import DiscreteDistributionHandmade
            dens = DiscreteDistributionHandmade(dens)
            z = Dummy('z', integer=True)
            space = SingleDiscretePSpace(z, dens)
            result = space.probability(condition.__class__(space.value, 0))
        return result if not cond_inv else S.One - result

    def compute_density(self, expr, **kwargs):
        rvs = random_symbols(expr)
        
        reps = self.values2symbols()
        for var in rvs:            
            expr = expr._subs(var, reps[var])

        assert not random_symbols(expr)

        if any(pspace(rv).is_Continuous for rv in rvs):
            z = Dummy('z', real=True)
            expr = self.compute_expectation(DiracDelta(expr - z),
             **kwargs)
        else:
            z = Dummy('z', integer=True)
            expr = self.compute_expectation(KroneckerDelta(expr, z),
             **kwargs)
        return Lambda(z, expr)

    def compute_cdf(self, expr, **kwargs):
        raise ValueError("CDF not well defined on multivariate expressions")

    def conditional_space(self, condition, normalize=True, **kwargs):
        rvs = random_symbols(condition)
        condition = condition.xreplace({rv: rv.symbol for rv in self.values})
        if any([pspace(rv).is_Continuous for rv in rvs]):
            from sympy.stats.crv import (ConditionalContinuousDomain,
                ContinuousPSpace)
            space = ContinuousPSpace
            domain = ConditionalContinuousDomain(self.domain, condition)
        elif any([pspace(rv).is_Discrete for rv in rvs]):
            from sympy.stats.drv import (ConditionalDiscreteDomain,
                DiscretePSpace)
            space = DiscretePSpace
            domain = ConditionalDiscreteDomain(self.domain, condition)
        elif all([pspace(rv).is_Finite for rv in rvs]):
            from sympy.stats.frv import FinitePSpace
            return FinitePSpace.conditional_space(self, condition)
        if normalize:
            replacement = {rv: Dummy(str(rv)) for rv in self.symbols}
            norm = domain.compute_expectation(self.pdf, **kwargs)
            pdf = self.pdf / norm.xreplace(replacement)
            # XXX: Converting symbols from set to tuple. The order matters to
            # Lambda though so we shouldn't be starting with a set here...
            density = Lambda(tuple(domain.symbols), pdf)

        return space(domain, density)

    @property
    def distribution(self):
        ...
        
class ProductDomain(RandomDomain):
    """
    A domain resulting from the merger of two independent domains

    See Also
    ========
    sympy.stats.crv.ProductContinuousDomain
    sympy.stats.frv.ProductFiniteDomain
    """
    is_ProductDomain = True

    def __new__(cls, *domains):
        # Flatten any product of products
        domains2 = []
        for domain in domains:
            if not domain.is_ProductDomain:
                domains2.append(domain)
            else:
                domains2.extend(domain.domains)
        domains2 = FiniteSet(*domains2)

        if all(domain.is_Finite for domain in domains2):
            from sympy.stats.frv import ProductFiniteDomain
            cls = ProductFiniteDomain
        if all(domain.is_Continuous for domain in domains2):
            from sympy.stats.crv import ProductContinuousDomain
            cls = ProductContinuousDomain
        if all(domain.is_Discrete for domain in domains2):
            from sympy.stats.drv import ProductDiscreteDomain
            cls = ProductDiscreteDomain

        return Basic.__new__(cls, *domains2)

    @property
    def sym_domain_dict(self):
        return {symbol: domain for domain in self.domains
                                     for symbol in domain.symbols}

    @property
    def symbols(self):
        return FiniteSet(*[sym for domain in self.domains
                               for sym    in domain.symbols])

    @property
    def domains(self):
        return self.args

    @property
    def set(self):
        return ProductSet(*(domain.set for domain in self.domains))

    def __contains__(self, other):
        # Split event into each subdomain
        for domain in self.domains:
            # Collect the parts of this event which associate to this domain
            elem = frozenset([item for item in other
                              if sympify(domain.symbols.contains(item[0]))
                              is S.true])
            # Test this sub-event
            if elem not in domain:
                return False
        # All subevents passed
        return True

    def as_boolean(self):
        return And(*[domain.as_boolean() for domain in self.domains])


def random_symbols(expr):
    
    """
    Returns all RandomSymbols within a SymPy Expression.
    """

    def preorder_traversal(self):
        if isinstance(self, Basic):            
            if self.is_symbol:
                if self.is_random:
                    yield self
            elif self.is_PDF:
                ...
            else:
                if hasattr(self, '_argset'):
                    args = self._argset
                else:
                    args = self.args
    
                for arg in args:
                    yield from preorder_traversal(arg)
                       
    return [*preorder_traversal(expr)]


def contain_random_symbols(expr):
    """
    Returns all RandomSymbols within a SymPy Expression.
    """
    from sympy.core.basic import preorder_traversal
    for ex in preorder_traversal(expr):
        from sympy.tensor.indexed import Indexed
        if isinstance(ex, Indexed):
            if ex.base.definition is not None:
                definition = ex.base.definition[ex.indices]
                if isinstance(definition, RandomSymbol) or contain_random_symbols(definition):
                    return True
        elif isinstance(ex, RandomSymbol):
            return True

    return False


def pspace(expr):
    """
    Returns the underlying Probability Space of a random expression.

    For internal use.

    Examples
    ========

    >>> from sympy.stats import pspace, Normal
    >>> X = Normal('X', 0, 1)
    >>> pspace(2*X + 1) == X.pspace
    True
    """
    expr = sympify(expr)
    if expr.is_symbol:
        assert expr.is_random
        if expr.is_integer:
            from sympy.stats.drv import SingleDiscretePSpace
            return SingleDiscretePSpace(expr)
        else:
            from sympy.stats.crv import SingleContinuousPSpace
            return SingleContinuousPSpace(expr)

    rvs = random_symbols(expr)
    if not rvs:
        raise ValueError("Expression containing Random Variable expected, not %s" % (expr))
    # If only one space present
    pspaces = {pspace(rv) for rv in rvs}
    if len(pspaces) == 1:
        ps, *_ = pspaces
        return ps
#     if all(ps == pspaces[0] for ps in pspaces):
#         return pspaces[0]    

    from sympy.stats.compound_rv import CompoundPSpace
    for ps in pspaces:
        if isinstance(ps, CompoundPSpace):
            return ps
    # Otherwise make a product space
    return IndependentProductPSpace(*pspaces)


def sumsets(sets):
    """
    Union of sets
    """
    return frozenset().union(*sets)


def rs_swap(fullspace, symbols2values):
    """
    Build a dictionary to swap RandomSymbols based on their underlying symbol.

    i.e.
    if    ``X = ('x', pspace1)``
    and   ``Y = ('x', pspace2)``
    then ``X`` and ``Y`` match and the key, value pair
    ``{X:Y}`` will appear in the result

    Inputs: collections a and b of random variables which share common symbols
    Output: dict mapping RVs in a to RVs in b
    """
    values2symbols = fullspace.values2symbols()
    swapdict = {}
    for value, symbol in values2symbols.items():
        if symbol in symbols2values:
            swapdict[value] = symbols2values[symbol]
    return swapdict


def given(expr, condition, **kwargs):
    r""" Conditional Random Expression
    From a random expression and a condition on that expression creates a new
    probability space from the condition and returns the same expression on that
    conditional probability space.

    Examples
    ========

    >>> from sympy.stats import given, density, Die
    >>> X = Die('X', 6)
    >>> Y = given(X, X > 3)
    >>> density(Y).dict
    {4: 1/3, 5: 1/3, 6: 1/3}

    Following convention, if the condition is a random symbol then that symbol
    is considered fixed.

    >>> from sympy.stats import Normal
    >>> from sympy import pprint
    >>> from sympy.abc import z

    >>> X = Normal('X', 0, 1)
    >>> Y = Normal('Y', 0, 1)
    >>> pprint(density(X + Y, Y)(z), use_unicode=False)
                    2
           -(-Y + z)
           -----------
      ___       2
    \/ 2 *e
    ------------------
             ____
         2*\/ pi
    """
    from sympy.stats.symbolic_probability import Conditioned
    if isinstance(expr, list):        
        return Conditioned(BlockMatrix(*expr), condition)
        
    if not condition.is_random or pspace_independent(expr, condition):
        return expr

#     if isinstance(condition, RandomSymbol):
    if condition.is_symbol:
        condition = Eq(condition, pspace(condition).symbol)

#     condsymbols = random_symbols(condition)
#     if condition.is_Equal and len(condsymbols) == 1 and not isinstance(pspace(expr).domain, ConditionalDomain):
#         rv = tuple(condsymbols)[0]
# 
#         results = solveset(condition, rv)
#         if isinstance(results, Intersection) and Reals in results.args:
#             results = list(results.args[1])
# 
#         sums = 0
#         for res in results:
#             temp = expr.subs(rv, res)
#             if temp == True:
#                 return True
#             if temp != False:
#                 # XXX: This seems nonsensical but preserves existing behaviour
#                 # after the change that Relational is no longer a subclass of
#                 # Expr. Here expr is sometimes Relational and sometimes Expr
#                 # but we are trying to add them with +=. This needs to be
#                 # fixed somehow.
#                 if sums == 0 and isinstance(expr, Relational):
#                     sums = expr.subs(rv, res)
#                 else:
#                     sums += expr.subs(rv, res)
#         if sums == 0:
#             return False
#         return sums

    # Get full probability space of both the expression and the condition
    fullspace = pspace(Tuple(expr, condition))
    # Build new space given the condition
    if fullspace.distribution:
        symbols2values = fullspace.conditional_space(condition, **kwargs)
        # Dictionary to swap out RandomSymbols in expr with new RandomSymbols
        # That point to the new conditional space
        swapdict = rs_swap(fullspace, symbols2values)
        # Swap random variables in the expression
        expr = expr.xreplace(swapdict)
        return expr
    else:        
        return Conditioned(expr, condition)


def expectation(expr, condition=None, numsamples=None, evaluate=True, **kwargs):
    """
    Returns the expected value of a random expression

    Parameters
    ==========

    expr : Expr containing RandomSymbols
        The expression of which you want to compute the expectation value
    given : Expr containing RandomSymbols
        A conditional expression. E(X, X>0) is expectation of X given X > 0
    numsamples : int
        Enables sampling and approximates the expectation with this many samples
    evalf : Bool (defaults to True)
        If sampling return a number rather than a complex expression
    evaluate : Bool (defaults to True)
        In case of continuous systems return unevaluated integral

    Examples
    ========

    >>> from sympy.stats import E, Die
    >>> X = Die('X', 6)
    >>> E(X)
    7/2
    >>> E(2*X + 1)
    8

    >>> E(X, X > 3) # Expectation of X given that it is above 3
    5
    """

    if not expr.is_random:  # expr isn't random?
        return expr
    kwargs['numsamples'] = numsamples
    from sympy.stats.symbolic_probability import Expectation
    if evaluate:
        return Expectation(expr, condition).doit(**kwargs)
    # ## TODO: Remove the user warnings in the future releases
    message = ("Since version 1.7, using `evaluate=False` returns `Expectation` "
              "object. If you want unevaluated Integral/Sum use "
              "`E(expr, condition, evaluate=False).rewrite(Integral)`")
    warnings.warn(filldedent(message))
    return Expectation(expr, condition)


def probability(condition, given_condition=None, numsamples=None,
                evaluate=True, **kwargs):
    """
    Probability that a condition is true, optionally given a second condition

    Parameters
    ==========

    condition : Combination of Relationals containing RandomSymbols
        The condition of which you want to compute the probability
    given_condition : Combination of Relationals containing RandomSymbols
        A conditional expression. P(X > 1, X > 0) is expectation of X > 1
        given X > 0
    numsamples : int
        Enables sampling and approximates the probability with this many samples
    evaluate : Bool (defaults to True)
        In case of continuous systems return unevaluated integral

    Examples
    ========

    >>> from sympy.stats import P, Die
    >>> from sympy import Eq
    >>> X, Y = Die('X', 6), Die('Y', 6)
    >>> P(X > 3)
    1/2
    >>> P(Eq(X, 5), X > 2) # Probability that X == 5 given that X > 2
    1/4
    >>> P(X > Y)
    5/12
    """

    kwargs['numsamples'] = numsamples
    from sympy.stats.symbolic_probability import Probability
    if evaluate:
        return Probability(condition, given_condition).doit(**kwargs)
    # ## TODO: Remove the user warnings in the future releases
    message = ("Since version 1.7, using `evaluate=False` returns `Probability` "
              "object. If you want unevaluated Integral/Sum use "
              "`P(condition, given_condition, evaluate=False).rewrite(Integral)`")
    warnings.warn(filldedent(message))
    return Probability(condition, given_condition)


class PDF(Basic):
    expr = property(lambda self: self.args[0])
    
    @property
    def condition(self):
        if len(self.args) > 1:
            return self.args[1]
        else:
            return None

    def doit(self, evaluate=True, **kwargs):
        from sympy.stats.random_matrix import RandomMatrixPSpace
        from sympy.stats.joint_rv import JointPSpace
        from sympy.stats.matrix_distributions import MatrixPSpace
        from sympy.stats.compound_rv import CompoundPSpace
        from sympy.stats.frv import SingleFiniteDistribution
        expr, condition = self.expr, self.condition

        if isinstance(expr, SingleFiniteDistribution):
            return expr.dict
        if condition is not None:
            # Recompute on new conditional expr
            expr = given(expr, condition, **kwargs)
        if not random_symbols(expr):
            x = Symbol('x', real=True)
            return Lambda(x, DiracDelta(x - expr))
        ps = pspace(expr)
        if expr.is_Symbol or expr.is_Indexed:
            if isinstance(ps, (SinglePSpace, JointPSpace, MatrixPSpace)) and \
                hasattr(ps, 'distribution'):
                return ps.distribution
            elif isinstance(ps, RandomMatrixPSpace):
                return ps.model
        if isinstance(ps, CompoundPSpace):
            kwargs['compound_evaluate'] = evaluate
        result = ps.compute_density(expr, **kwargs)

        if evaluate and hasattr(result, 'doit'):
            return result.doit()
        else:
            return result

    def __call__(self, *args):
        return PDFInvoker(self, *args)


# probability mass function for discrete random variables, probability density function for continuous random variables
class PDFInvoker(Expr):    
    is_nonnegative = True
      
    @property
    def symbol(self):
        return self.args[1]

    @property
    def density(self):
        return self.args[0]

    def doit(self, evaluate=True, **kwargs):
        result = self.density.doit(evaluate)
        return result(*self.args[1:])
    
    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.real

    def _sympystr(self, p):
        expr, symbols = self.args

        symbols = p._print(symbols)

        tex = r"%s(%s)" % (p._print(expr), symbols)

        return tex

    def _latex(self, p):
        expr, symbols = self.args

        symbols = p._print(symbols)

        tex = r"%s\left(%s \right)" % (p._print(expr), symbols)

        return tex


def density(expr, condition=None, evaluate=True, numsamples=None, **kwargs):
    """
    Probability density of a random expression, optionally given a second
    condition.

    This density will take on different forms for different types of
    probability spaces. Discrete variables produce Dicts. Continuous
    variables produce Lambdas.

    Parameters
    ==========

    expr : Expr containing RandomSymbols
        The expression of which you want to compute the density value
    condition : Relational containing RandomSymbols
        A conditional expression. density(X > 1, X > 0) is density of X > 1
        given X > 0
    numsamples : int
        Enables sampling and approximates the density with this many samples

    Examples
    ========

    >>> from sympy.stats import density, Die, Normal
    >>> from sympy import Symbol

    >>> x = Symbol('x')
    >>> D = Die('D', 6)
    >>> X = Normal(x, 0, 1)

    >>> density(D).dict
    {1: 1/6, 2: 1/6, 3: 1/6, 4: 1/6, 5: 1/6, 6: 1/6}
    >>> density(2*D).dict
    {2: 1/6, 4: 1/6, 6: 1/6, 8: 1/6, 10: 1/6, 12: 1/6}
    >>> density(X)(x)
    sqrt(2)*exp(-x**2/2)/(2*sqrt(pi))
    """

    if numsamples:
        return sampling_density(expr, condition, numsamples=numsamples,
                **kwargs)

    return PDF(expr, condition).doit(evaluate=evaluate, **kwargs)


def cdf(expr, condition=None, evaluate=True, **kwargs):
    """
    Cumulative Distribution Function of a random expression.

    optionally given a second condition

    This density will take on different forms for different types of
    probability spaces.
    Discrete variables produce Dicts.
    Continuous variables produce Lambdas.

    Examples
    ========

    >>> from sympy.stats import density, Die, Normal, cdf

    >>> D = Die('D', 6)
    >>> X = Normal('X', 0, 1)

    >>> density(D).dict
    {1: 1/6, 2: 1/6, 3: 1/6, 4: 1/6, 5: 1/6, 6: 1/6}
    >>> cdf(D)
    {1: 1/6, 2: 1/3, 3: 1/2, 4: 2/3, 5: 5/6, 6: 1}
    >>> cdf(3*D, D > 2)
    {9: 1/4, 12: 1/2, 15: 3/4, 18: 1}

    >>> cdf(X)
    Lambda(_z, erf(sqrt(2)*_z/2)/2 + 1/2)
    """
    if condition is not None:  # If there is a condition
        # Recompute on new conditional expr
        return cdf(given(expr, condition, **kwargs), **kwargs)

    # Otherwise pass work off to the ProbabilitySpace
    result = pspace(expr).compute_cdf(expr, **kwargs)

    if evaluate and hasattr(result, 'doit'):
        return result.doit()
    else:
        return result


def characteristic_function(expr, condition=None, evaluate=True, **kwargs):
    """
    Characteristic function of a random expression, optionally given a second condition

    Returns a Lambda

    Examples
    ========

    >>> from sympy.stats import Normal, DiscreteUniform, Poisson, characteristic_function

    >>> X = Normal('X', 0, 1)
    >>> characteristic_function(X)
    Lambda(_t, exp(-_t**2/2))

    >>> Y = DiscreteUniform('Y', [1, 2, 7])
    >>> characteristic_function(Y)
    Lambda(_t, exp(7*_t*I)/3 + exp(2*_t*I)/3 + exp(_t*I)/3)

    >>> Z = Poisson('Z', 2)
    >>> characteristic_function(Z)
    Lambda(_t, exp(2*exp(_t*I) - 2))
    """
    if condition is not None:
        return characteristic_function(given(expr, condition, **kwargs), **kwargs)

    result = pspace(expr).compute_characteristic_function(expr, **kwargs)

    if evaluate and hasattr(result, 'doit'):
        return result.doit()
    else:
        return result


def moment_generating_function(expr, condition=None, evaluate=True, **kwargs):
    if condition is not None:
        return moment_generating_function(given(expr, condition, **kwargs), **kwargs)

    result = pspace(expr).compute_moment_generating_function(expr, **kwargs)

    if evaluate and hasattr(result, 'doit'):
        return result.doit()
    else:
        return result


def where(condition, given_condition=None, **kwargs):
    """
    Returns the domain where a condition is True.

    Examples
    ========

    >>> from sympy.stats import where, Die, Normal
    >>> from sympy import And

    >>> D1, D2 = Die('a', 6), Die('b', 6)
    >>> a, b = D1.symbol, D2.symbol
    >>> X = Normal('x', 0, 1)

    >>> where(X**2<1)
    Domain: (-1 < x) & (x < 1)

    >>> where(X**2<1).set
    Interval.open(-1, 1)

    >>> where(And(D1<=D2 , D2<3))
    Domain: (Eq(a, 1) & Eq(b, 1)) | (Eq(a, 1) & Eq(b, 2)) | (Eq(a, 2) & Eq(b, 2))
    """
    if given_condition is not None:  # If there is a condition
        # Recompute on new conditional expr
        return where(given(condition, given_condition, **kwargs), **kwargs)

    # Otherwise pass work off to the ProbabilitySpace
    return pspace(condition).where(condition, **kwargs)


def sample(expr, condition=None, size=(), library='scipy', numsamples=1,
                                                                    **kwargs):
    """
    A realization of the random expression

    Parameters
    ==========

    expr : Expression of random variables
        Expression from which sample is extracted
    condition : Expr containing RandomSymbols
        A conditional expression
    size : int, tuple
        Represents size of each sample in numsamples
    library : str
        - 'scipy' : Sample using scipy
        - 'numpy' : Sample using numpy
        - 'pymc3' : Sample using PyMC3

        Choose any of the available options to sample from as string,
        by default is 'scipy'
    numsamples : int
        Number of samples, each with size as ``size``

    Examples
    ========

    >>> from sympy.stats import Die, sample, Normal, Geometric
    >>> X, Y, Z = Die('X', 6), Die('Y', 6), Die('Z', 6) # Finite Random Variable

    >>> die_roll = sample(X + Y + Z) # doctest: +SKIP
    >>> next(die_roll) # doctest: +SKIP
    6
    >>> N = Normal('N', 3, 4) # Continuous Random Variable
    >>> samp = next(sample(N)) # doctest: +SKIP
    >>> samp in N.pspace.domain.set # doctest: +SKIP
    True
    >>> samp = next(sample(N, N>0)) # doctest: +SKIP
    >>> samp > 0 # doctest: +SKIP
    True
    >>> samp_list = next(sample(N, size=4)) # doctest: +SKIP
    >>> [sam in N.pspace.domain.set for sam in samp_list] # doctest: +SKIP
    [True, True, True, True]
    >>> G = Geometric('G', 0.5) # Discrete Random Variable
    >>> samp_list = next(sample(G, size=3)) # doctest: +SKIP
    >>> samp_list # doctest: +SKIP
    array([10,  4,  1])
    >>> [sam in G.pspace.domain.set for sam in samp_list] # doctest: +SKIP
    [True, True, True]
    >>> MN = Normal("MN", [3, 4], [[2, 1], [1, 2]]) # Joint Random Variable
    >>> samp_list = next(sample(MN, size=4)) # doctest: +SKIP
    >>> samp_list # doctest: +SKIP
    array([[4.22564264, 3.23364418],
           [3.41002011, 4.60090908],
           [3.76151866, 4.77617143],
           [4.71440865, 2.65714157]])
    >>> [tuple(sam) in MN.pspace.domain.set for sam in samp_list] # doctest: +SKIP
    [True, True, True, True]


    Returns
    =======

    sample: iterator object
        iterator object containing the sample/samples of given expr

    """
    # ## TODO: Remove the user warnings in the future releases
    message = ("The return type of sample has been changed to return an "
                  "iterator object since version 1.7. For more information see "
                  "https://github.com/sympy/sympy/issues/19061")
    warnings.warn(filldedent(message))
    return sample_iter(expr, condition, size=size, library=library,
                                                        numsamples=numsamples)


def quantile(expr, evaluate=True, **kwargs):
    r"""
    Return the :math:`p^{th}` order quantile of a probability distribution.

    Quantile is defined as the value at which the probability of the random
    variable is less than or equal to the given probability.

    ..math::
        Q(p) = inf{x \in (-\infty, \infty) such that p <= F(x)}

    Examples
    ========

    >>> from sympy.stats import quantile, Die, Exponential
    >>> from sympy import Symbol, pprint
    >>> p = Symbol("p")

    >>> l = Symbol("lambda", positive=True)
    >>> X = Exponential("x", l)
    >>> quantile(X)(p)
    -log(1 - p)/lambda

    >>> D = Die("d", 6)
    >>> pprint(quantile(D)(p), use_unicode=False)
    /nan  for Or(p > 1, p < 0)
    |
    | 1       for p <= 1/6
    |
    | 2       for p <= 1/3
    |
    < 3       for p <= 1/2
    |
    | 4       for p <= 2/3
    |
    | 5       for p <= 5/6
    |
    \ 6        for p <= 1

    """
    result = pspace(expr).compute_quantile(expr, **kwargs)

    if evaluate and hasattr(result, 'doit'):
        return result.doit()
    else:
        return result


def sample_iter(expr, condition=None, size=(), library='scipy',
                    numsamples=S.Infinity, **kwargs):

    """
    Returns an iterator of realizations from the expression given a condition

    Parameters
    ==========

    expr: Expr
        Random expression to be realized
    condition: Expr, optional
        A conditional expression
    size : int, tuple
        Represents size of each sample in numsamples
    numsamples: integer, optional
        Length of the iterator (defaults to infinity)

    Examples
    ========

    >>> from sympy.stats import Normal, sample_iter
    >>> X = Normal('X', 0, 1)
    >>> expr = X*X + 3
    >>> iterator = sample_iter(expr, numsamples=3) # doctest: +SKIP
    >>> list(iterator) # doctest: +SKIP
    [12, 4, 7]

    Returns
    =======

    sample_iter: iterator object
        iterator object containing the sample/samples of given expr

    See Also
    ========

    sample
    sampling_P
    sampling_E

    """
    from sympy.stats.joint_rv import JointRandomSymbol
    if not import_module(library):
        raise ValueError("Failed to import %s" % library)

    if condition is not None:
        ps = pspace(Tuple(expr, condition))
    else:
        ps = pspace(expr)

    rvs = list(ps.values)
    if isinstance(expr, JointRandomSymbol):
        expr = expr.subs({expr: RandomSymbol(expr.symbol, expr.pspace)})
    else:
        sub = {}
        for arg in expr.args:
            if isinstance(arg, JointRandomSymbol):
                sub[arg] = RandomSymbol(arg.symbol, arg.pspace)
        expr = expr.subs(sub)

    if library == 'pymc3':
        # Currently unable to lambdify in pymc3
        # TODO : Remove 'pymc3' when lambdify accepts 'pymc3' as module
        fn = lambdify(rvs, expr, **kwargs)
    else:
        fn = lambdify(rvs, expr, modules=library, **kwargs)
    if condition is not None:
        given_fn = lambdify(rvs, condition, **kwargs)

    def return_generator():
        count = 0
        while count < numsamples:
            d = ps.sample(size=size, library=library)  # a dictionary that maps RVs to values
            args = [d[rv] for rv in rvs]

            if condition is not None:  # Check that these values satisfy the condition
                gd = given_fn(*args)
                if gd != True and gd != False:
                    raise ValueError(
                        "Conditions must not contain free symbols")
                if not gd:  # If the values don't satisfy then try again
                    continue

            yield fn(*args)
            count += 1

    return return_generator()


def sample_iter_lambdify(expr, condition=None, size=(), numsamples=S.Infinity,
                                                                    **kwargs):

    return sample_iter(expr, condition=condition, size=size, numsamples=numsamples,
                                                                        **kwargs)


def sample_iter_subs(expr, condition=None, size=(), numsamples=S.Infinity,
                                                                    **kwargs):

    return sample_iter(expr, condition=condition, size=size, numsamples=numsamples,
                                                                        **kwargs)


def sampling_P(condition, given_condition=None, library='scipy', numsamples=1,
                                                    evalf=True, **kwargs):
    """
    Sampling version of P

    See Also
    ========

    P
    sampling_E
    sampling_density

    """

    count_true = 0
    count_false = 0

    samples = sample_iter(condition, given_condition, library=library,
                          numsamples=numsamples, **kwargs)

    for sample in samples:
        if sample:
            count_true += 1
        else:
            count_false += 1

    result = S(count_true) / numsamples
    if evalf:
        return result.evalf()
    else:
        return result


def sampling_E(expr, given_condition=None, library='scipy', numsamples=1,
               evalf=True, **kwargs):
    """
    Sampling version of E

    See Also
    ========

    P
    sampling_P
    sampling_density
    """
    samples = list(sample_iter(expr, given_condition, library=library,
                          numsamples=numsamples, **kwargs))
    result = Add(*[samp for samp in samples]) / numsamples

    if evalf:
        return result.evalf()
    else:
        return result


def sampling_density(expr, given_condition=None, library='scipy',
                    numsamples=1, **kwargs):
    """
    Sampling version of density

    See Also
    ========
    density
    sampling_P
    sampling_E
    """

    results = {}
    for result in sample_iter(expr, given_condition, library=library,
                              numsamples=numsamples, **kwargs):
        results[result] = results.get(result, 0) + 1

    return results


def dependent(a, b):
    """
    Dependence of two random expressions

    Two expressions are independent if knowledge of one does not change
    computations on the other.

    Examples
    ========

    >>> from sympy.stats import Normal, dependent, given
    >>> from sympy import Tuple, Eq

    >>> X, Y = Normal('X', 0, 1), Normal('Y', 0, 1)
    >>> dependent(X, Y)
    False
    >>> dependent(2*X + Y, -Y)
    True
    >>> X, Y = given(Tuple(X, Y), Eq(X + Y, 3))
    >>> dependent(X, Y)
    True

    See Also
    ========

    independent
    """
    if pspace_independent(a, b):
        return False

    z = Symbol('z', real=True)
    # Dependent if density is unchanged when one is given information about
    # the other
    return (density(a, Eq(b, z)) != density(a) or
            density(b, Eq(a, z)) != density(b))


def independent(a, b):
    """
    Independence of two random expressions

    Two expressions are independent if knowledge of one does not change
    computations on the other.

    Examples
    ========

    >>> from sympy.stats import Normal, independent, given
    >>> from sympy import Tuple, Eq

    >>> X, Y = Normal('X', 0, 1), Normal('Y', 0, 1)
    >>> independent(X, Y)
    True
    >>> independent(2*X + Y, -Y)
    False
    >>> X, Y = given(Tuple(X, Y), Eq(X + Y, 3))
    >>> independent(X, Y)
    False

    See Also
    ========

    dependent
    """
    return not dependent(a, b)


def pspace_independent(a, b):
    """
    Tests for independence between a and b by checking if their PSpaces have
    overlapping symbols. This is a sufficient but not necessary condition for
    independence and is intended to be used internally.

    Notes
    =====

    pspace_independent(a, b) implies independent(a, b)
    independent(a, b) does not imply pspace_independent(a, b)
    """
    pspace_a = pspace(a)
    pspace_b = pspace(b)
    if pspace_a.distribution is None or pspace_b.distribution is None:
        return 
    a_symbols = set(pspace_a.symbols)
    b_symbols = set(pspace_b.symbols)

    if len(set(random_symbols(a)).intersection(random_symbols(b))) != 0:
        return False

    if len(a_symbols.intersection(b_symbols)) == 0:
        return True


def rv_subs(expr, symbols=None):
    """
    Given a random expression replace all random variables with their symbols.

    If symbols keyword is given restrict the swap to only the symbols listed.
    """
    if symbols is None:
        symbols = random_symbols(expr)
    if not symbols:
        return expr
    swapdict = {rv: rv.symbol for rv in symbols}
    return expr.subs(swapdict)


class NamedArgsMixin:
    _argnames = ()  # type: tTuple[str, ...]

    def __getattr__(self, attr):
        try:
            return self.args[self._argnames.index(attr)]
        except ValueError:
            raise AttributeError("'%s' object has no attribute '%s'" % (
                type(self).__name__, attr))


def _value_check(condition, message):
    """
    Raise a ValueError with message if condition is False, else
    return True if all conditions were True, else False.

    Examples
    ========

    >>> from sympy.stats.rv import _value_check
    >>> from sympy.abc import a, b, c
    >>> from sympy import And, Dummy

    >>> _value_check(2 < 3, '')
    True

    Here, the condition is not False, but it doesn't evaluate to True
    so False is returned (but no error is raised). So checking if the
    return value is True or False will tell you if all conditions were
    evaluated.

    >>> _value_check(a < b, '')
    False

    In this case the condition is False so an error is raised:

    >>> r = Dummy(real=True)
    >>> _value_check(r < r - 1, 'condition is not true')
    Traceback (most recent call last):
    ...
    ValueError: condition is not true

    If no condition of many conditions must be False, they can be
    checked by passing them as an iterable:

    >>> _value_check((a < 0, b < 0, c < 0), '')
    False

    The iterable can be a generator, too:

    >>> _value_check((i < 0 for i in (a, b, c)), '')
    False

    The following are equivalent to the above but do not pass
    an iterable:

    >>> all(_value_check(i < 0, '') for i in (a, b, c))
    False
    >>> _value_check(And(a < 0, b < 0, c < 0), '')
    False
    """
    from sympy.core.compatibility import iterable
    from sympy.core.logic import fuzzy_and
    if not iterable(condition):
        condition = [condition]
    truth = fuzzy_and(condition)
    if truth == False:
        raise ValueError(message)
    return truth == True


def _symbol_converter(sym):
    """
    Casts the parameter to Symbol if it is 'str'
    otherwise no operation is performed on it.

    Parameters
    ==========

    sym
        The parameter to be converted.

    Returns
    =======

    Symbol
        the parameter converted to Symbol.

    Raises
    ======

    TypeError
        If the parameter is not an instance of both str and
        Symbol.

    Examples
    ========

    >>> from sympy import Symbol
    >>> from sympy.stats.rv import _symbol_converter
    >>> s = _symbol_converter('s')
    >>> isinstance(s, Symbol)
    True
    >>> _symbol_converter(1)
    Traceback (most recent call last):
    ...
    TypeError: 1 is neither a Symbol nor a string
    >>> r = Symbol('r')
    >>> isinstance(r, Symbol)
    True
    """
    if isinstance(sym, str):
            sym = Symbol(sym)
    if not isinstance(sym, (Symbol, Indexed)):
        raise TypeError("%s is neither a Symbol nor a string" % (sym))
    return sym


def sample_stochastic_process(process):
    """
    This function is used to sample from stochastic process.

    Parameters
    ==========

    process: StochasticProcess
        Process used to extract the samples. It must be an instance of
        StochasticProcess

    Examples
    ========

    >>> from sympy.stats import sample_stochastic_process, DiscreteMarkovChain
    >>> from sympy import Matrix
    >>> T = Matrix([[0.5, 0.2, 0.3],[0.2, 0.5, 0.3],[0.2, 0.3, 0.5]])
    >>> Y = DiscreteMarkovChain("Y", [0, 1, 2], T)
    >>> next(sample_stochastic_process(Y)) in Y.state_space # doctest: +SKIP
    True
    >>> next(sample_stochastic_process(Y))  # doctest: +SKIP
    0
    >>> next(sample_stochastic_process(Y)) # doctest: +SKIP
    2

    Returns
    =======

    sample: iterator object
        iterator object containing the sample of given process

    """
    from sympy.stats.stochastic_process_types import StochasticProcess
    if not isinstance(process, StochasticProcess):
        raise ValueError("Process must be an instance of Stochastic Process")
    return process.sample()

class Distribution(Basic):
    def __call__(self, *args):
        return self.pdf(*args)
    
    @property
    def type(self):
        return dtype.distribution   

    def _latex(self, p):
        name = self.func.__name__[:-len('Distribution')]
        return name + p._print(self.args)