from sympy import (Basic, sympify, symbols, Dummy, Lambda, summation,
                   Piecewise, S, cacheit, Sum, exp, I, Ne, Eq, poly,
                   series, factorial, And, lambdify)

from sympy.polys.polyerrors import PolynomialError
from sympy.stats.crv import reduce_rational_inequalities_wrap
from sympy.stats.rv import (NamedArgsMixin, SinglePSpace, SingleDomain,
                            PSpace, ConditionalDomain, RandomDomain,
                            ProductDomain, Distribution)
from sympy.stats.symbolic_probability import Probability
from sympy.sets.fancysets import Range, FiniteSet
from sympy.sets.sets import Union
from sympy.sets.contains import Element
from sympy.utilities import filldedent
from sympy.core.sympify import _sympify
from sympy.external import import_module
from sympy.sets import Integers


class DiscreteDistribution(Distribution):
    is_integer = True


class SampleDiscreteScipy:
    """Returns the sample from scipy of the given distribution"""

    def __new__(cls, dist, size):
        return cls._sample_scipy(dist, size)

    @classmethod
    def _sample_scipy(cls, dist, size):
        """Sample from SciPy."""

        from scipy import stats as scipy_stats
        scipy_rv_map = {
            'GeometricDistribution': lambda dist, size: scipy_stats.geom.rvs(p=float(dist.p),
                size=size),
            'LogarithmicDistribution': lambda dist, size: scipy_stats.logser.rvs(p=float(dist.p),
                size=size),
            'NegativeBinomialDistribution': lambda dist, size: scipy_stats.nbinom.rvs(n=float(dist.r),
                p=float(dist.p), size=size),
            'PoissonDistribution': lambda dist, size: scipy_stats.poisson.rvs(mu=float(dist.lamda),
                size=size),
            'SkellamDistribution': lambda dist, size: scipy_stats.skellam.rvs(mu1=float(dist.mu1),
                mu2=float(dist.mu2), size=size),
            'YuleSimonDistribution': lambda dist, size: scipy_stats.yulesimon.rvs(alpha=float(dist.rho),
                size=size),
            'ZetaDistribution': lambda dist, size: scipy_stats.zipf.rvs(a=float(dist.s),
                size=size)
        }

        dist_list = scipy_rv_map.keys()

        if dist.__class__.__name__ == 'DiscreteDistributionHandmade':
            from scipy.stats import rv_discrete
            z = Dummy('z')
            handmade_pmf = lambdify(z, dist.pdf(z), 'scipy')

            class scipy_pmf(rv_discrete):

                def _pmf(self, x):
                    return handmade_pmf(x)

            scipy_rv = scipy_pmf(a=float(dist.set._inf), b=float(dist.set._sup),
                        name='scipy_pmf')
            return scipy_rv.rvs(size=size)

        if dist.__class__.__name__ not in dist_list:
            return None

        return scipy_rv_map[dist.__class__.__name__](dist, size)


class SampleDiscreteNumpy:
    """Returns the sample from numpy of the given distribution"""

    def __new__(cls, dist, size):
        return cls._sample_numpy(dist, size)

    @classmethod
    def _sample_numpy(cls, dist, size):
        """Sample from NumPy."""

        import numpy
        numpy_rv_map = {
            'GeometricDistribution': lambda dist, size: numpy.random.geometric(p=float(dist.p),
                size=size),
            'PoissonDistribution': lambda dist, size: numpy.random.poisson(lam=float(dist.lamda),
                size=size),
            'ZetaDistribution': lambda dist, size: numpy.random.zipf(a=float(dist.s),
                size=size)
        }

        dist_list = numpy_rv_map.keys()

        if dist.__class__.__name__ not in dist_list:
            return None

        return numpy_rv_map[dist.__class__.__name__](dist, size)


class SampleDiscretePymc:
    """Returns the sample from pymc3 of the given distribution"""

    def __new__(cls, dist, size):
        return cls._sample_pymc3(dist, size)

    @classmethod
    def _sample_pymc3(cls, dist, size):
        """Sample from PyMC3."""

        import pymc3
        pymc3_rv_map = {
            'GeometricDistribution': lambda dist: pymc3.Geometric('X', p=float(dist.p)),
            'PoissonDistribution': lambda dist: pymc3.Poisson('X', mu=float(dist.lamda)),
            'NegativeBinomialDistribution': lambda dist: pymc3.NegativeBinomial('X',
            mu=float((dist.p * dist.r) / (1 - dist.p)), alpha=float(dist.r))
        }

        dist_list = pymc3_rv_map.keys()

        if dist.__class__.__name__ not in dist_list:
            return None

        with pymc3.Model():
            pymc3_rv_map[dist.__class__.__name__](dist)
            return pymc3.sample(size, chains=1, progressbar=False)[:]['X']


_get_sample_class_drv = {
    'scipy': SampleDiscreteScipy,
    'pymc3': SampleDiscretePymc,
    'numpy': SampleDiscreteNumpy
}


class SingleDiscreteDistribution(DiscreteDistribution, NamedArgsMixin):
    """ Discrete distribution of a single variable

    Serves as superclass for PoissonDistribution etc....

    Provides methods for pdf, cdf, and sampling

    See Also:
        sympy.stats.crv_types.*
    """
    
    domain = set = Integers

    def __new__(cls, *args):
        args = list(map(sympify, args))
        return Basic.__new__(cls, *args)

    @staticmethod
    def check(*args):
        pass

    def sample(self, size=(), library='scipy'):
        """ A random realization from the distribution"""

        libraries = ['scipy', 'numpy', 'pymc3']
        if library not in libraries:
            raise NotImplementedError("Sampling from %s is not supported yet."
                                        % str(library))
        if not import_module(library):
            raise ValueError("Failed to import %s" % library)

        samps = _get_sample_class_drv[library](self, size)

        if samps is not None:
            return samps
        raise NotImplementedError(
                "Sampling for %s is not currently implemented from %s"
                % (self.__class__.__name__, library)
                )

    @cacheit
    def compute_cdf(self, **kwargs):
        """ Compute the CDF from the PDF

        Returns a Lambda
        """
        x, z = symbols('x, z', integer=True, cls=Dummy)
        left_bound = self.set.inf

        # CDF is integral of PDF from left bound to z
        pdf = self.pdf(x)
        cdf = summation(pdf, (x, left_bound, z), **kwargs)
        # CDF Ensure that CDF left of left_bound is zero
        cdf = Piecewise((cdf, z >= left_bound), (0, True))
        return Lambda(z, cdf)

    def _cdf(self, x):
        return None

    def cdf(self, x, **kwargs):
        """ Cumulative density function """
        if not kwargs:
            cdf = self._cdf(x)
            if cdf is not None:
                return cdf
        return self.compute_cdf(**kwargs)(x)

    @cacheit
    def compute_characteristic_function(self, **kwargs):
        """ Compute the characteristic function from the PDF

        Returns a Lambda
        """
        x, t = symbols('x, t', real=True, cls=Dummy)
        pdf = self.pdf(x)
        cf = summation(exp(I * t * x) * pdf, (x, self.set.inf, self.set.sup))
        return Lambda(t, cf)

    def _characteristic_function(self, t):
        return None

    def characteristic_function(self, t, **kwargs):
        """ Characteristic function """
        if not kwargs:
            cf = self._characteristic_function(t)
            if cf is not None:
                return cf
        return self.compute_characteristic_function(**kwargs)(t)

    @cacheit
    def compute_moment_generating_function(self, **kwargs):
        t = Dummy('t', real=True)
        x = Dummy('x', integer=True)
        pdf = self.pdf(x)
        mgf = summation(exp(t * x) * pdf, (x, self.domain.min(), self.domain.max()))
        return Lambda(t, mgf)

    def _moment_generating_function(self, t):
        return None

    def moment_generating_function(self, t, **kwargs):
        if not kwargs:
            mgf = self._moment_generating_function(t)
            if mgf is not None:
                return mgf
        return self.compute_moment_generating_function(**kwargs)(t)

    @cacheit
    def compute_quantile(self, **kwargs):
        """ Compute the Quantile from the PDF

        Returns a Lambda
        """
        x = Dummy('x', integer=True)
        p = Dummy('p', real=True)
        left_bound = self.set.inf
        pdf = self.pdf(x)
        cdf = summation(pdf, (x, left_bound, x), **kwargs)
        set = ((x, p <= cdf),)
        return Lambda(p, Piecewise(*set))

    def _quantile(self, x):
        return None

    def quantile(self, x, **kwargs):
        """ Cumulative density function """
        if not kwargs:
            quantile = self._quantile(x)
            if quantile is not None:
                return quantile
        return self.compute_quantile(**kwargs)(x)

    def expectation(self, expr, var, evaluate=True, **kwargs):
        """ Expectation of expression over distribution """
        # TODO: support discrete sets with non integer stepsizes

        return Sum[var:self.domain.min(): self.domain.max() + 1](expr * self(var)).doit(evaluate=evaluate)

    def __call__(self, *args):
        return self.pdf(*args)


class DiscreteDomain(RandomDomain):
    """
    A domain with discrete support with step size one.
    Represented using symbols and Range.
    """
    is_Discrete = True


class SingleDiscreteDomain(DiscreteDomain, SingleDomain):

    def as_boolean(self):
        return Element(self.symbol, self.set)


class ConditionalDiscreteDomain(DiscreteDomain, ConditionalDomain):
    """
    Domain with discrete support of step size one, that is restricted by
    some condition.
    """

    @property
    def set(self):
        rv = self.symbols
        if len(self.symbols) > 1:
            raise NotImplementedError(filldedent('''
                Multivariate conditional domains are not yet implemented.'''))
        rv = list(rv)[0]
        return reduce_rational_inequalities_wrap(self.condition,
            rv).intersect(self.fulldomain.set)


class DiscretePSpace(PSpace):
    is_real = True
    is_Discrete = True

    @property
    def value(self):
        return self.args[-1]

    @property
    def values(self):
        return {self.value}

    def values2symbols(self):
        return {self.value: self.symbol}
    
    def symbols2values(self):
        return {self.symbol: self.value}

    @property
    def pdf(self):
        return self.density(*self.symbols)

    def where(self, condition):
        rvs = condition.random_symbols
        assert all(r in self.values for r in rvs)
        if len(rvs) > 1:
            raise NotImplementedError(filldedent('''Multivariate discrete
            random variables are not yet supported.'''))
        conditional_domain = reduce_rational_inequalities_wrap(condition,
            rvs[0])
        conditional_domain = conditional_domain.intersect(self.domain.set)
        return SingleDiscreteDomain(self.symbol, conditional_domain)

    def probability(self, condition):
        complement = isinstance(condition, Ne)
        if complement:
            condition = Eq(condition.args[0], condition.args[1])
        try:
            _domain = self.value.domain_conditioned(condition)
            if condition == False or _domain.is_EmptySet:
                return S.Zero
            if condition == True or _domain == self.domain:
                return S.One
            prob = self.eval_prob(_domain)
        except NotImplementedError:
            from sympy.stats.rv import density
            expr = condition.lhs - condition.rhs
            dens = density(expr)
            if not isinstance(dens, DiscreteDistribution):
                from sympy.stats.drv_types import DiscreteDistributionHandmade
                dens = DiscreteDistributionHandmade(dens)
            z = Dummy('z', real=True)
            space = SingleDiscretePSpace(z, dens)
            prob = space.probability(condition.__class__(space.value, 0))
        if prob is None:
            prob = Probability(condition)
        return prob if not complement else S.One - prob

    def eval_prob(self, _domain):
        return Sum[self.symbol:_domain](self.distribution.pdf(self.symbol)).simplify()

    def conditional_space(self, condition):
        # XXX: Converting from set to tuple. The order matters to Lambda
        # though so we should be starting with a set...
        density = Lambda(tuple(self.symbols), self.pdf / self.probability(condition))
        domain_conditioned = self.value.domain_conditioned(condition)
        
        #         condition = condition.xreplace(self.values2symbols())        
#         domain = ConditionalDiscreteDomain(self.domain, condition)
        from sympy.stats.drv_types import AbstractDiscreteDistribution
        value = self.value.copy(distribution=AbstractDiscreteDistribution(density, domain_conditioned))
        return {self.symbol : value}


class ProductDiscreteDomain(ProductDomain, DiscreteDomain):

    def as_boolean(self):
        return And(*[domain.as_boolean for domain in self.domains])


class SingleDiscretePSpace(DiscretePSpace, SinglePSpace):
    """ Discrete probability space over a single univariate variable """
    is_real = True

    @property
    def symbols(self):
        return {self.symbol}

    @property
    def set(self):
        return self.distribution.set

    domain = set

    def sample(self, size=(), library='scipy'):
        """
        Internal sample method

        Returns dictionary mapping RandomSymbol to realization value.
        """
        return {self.value: self.distribution.sample(size, library=library)}

    def compute_expectation(self, expr, rvs=None, evaluate=True, **kwargs):
        rvs = rvs or (self.value,)
        if self.value not in rvs:
            return expr

        expr = _sympify(expr)
        if expr.is_random:            
            expr = expr.xreplace(self.values2symbols())

        x = self.symbol
        try:
            return self.distribution.expectation(expr, x, evaluate=evaluate,
                    **kwargs)
        except NotImplementedError:
            return Sum[x:self.domain](expr * self.pdf)

    def compute_cdf(self, expr, **kwargs):
        if expr == self.value:
            x = Dummy("x", real=True)
            return Lambda(x, self.distribution.cdf(x, **kwargs))
        else:
            raise NotImplementedError()

    def compute_density(self, expr, **kwargs):
        if expr == self.value:
            return self.distribution
        raise NotImplementedError()

    def compute_characteristic_function(self, expr, **kwargs):
        if expr == self.value:
            t = Dummy("t", real=True)
            return Lambda(t, self.distribution.characteristic_function(t, **kwargs))
        else:
            raise NotImplementedError()

    def compute_moment_generating_function(self, expr, **kwargs):
        if expr == self.value:
            t = Dummy("t", real=True)
            return Lambda(t, self.distribution.moment_generating_function(t, **kwargs))
        else:
            raise NotImplementedError()

    def compute_quantile(self, expr, **kwargs):
        if expr == self.value:
            p = Dummy("p", real=True)
            return Lambda(p, self.distribution.quantile(p, **kwargs))
        else:
            raise NotImplementedError()
