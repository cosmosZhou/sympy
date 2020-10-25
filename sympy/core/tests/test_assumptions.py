from sympy import I, sqrt, log, exp, sin, asin, factorial, Mod, pi, oo
from sympy.core import Symbol, S, Rational, Integer, Dummy, Wild, Pow
from sympy.core.assumptions import (assumptions, check_assumptions,
    failing_assumptions, common_assumptions)
from sympy.core.facts import InconsistentAssumptions
from sympy import simplify

from sympy.testing.pytest import raises, XFAIL


def test_symbol_unset():
    x = Symbol('x', real=True, integer=True)
    assert x.is_real == True
    assert x.is_integer == True
    assert x.is_imaginary == False
    assert x.is_noninteger is False
    assert x.is_number is False


def test_zero():
    z = Integer(0)
    assert z.is_commutative == True
    assert z.is_integer == True
    assert z.is_rational == True
    assert z.is_algebraic == True
    assert z.is_transcendental is False
    assert z.is_real == True
    assert z.is_complex == True
    assert z.is_noninteger is False
    assert z.is_irrational is False
    assert z.is_imaginary == False
    assert z.is_positive == False
    assert z.is_negative == False
    assert z.is_nonpositive == True
    assert z.is_nonnegative == True
    assert z.is_even == True
    assert z.is_odd == False
    assert z.is_finite == True
    assert z.is_infinite is False
    assert z.is_comparable is True
    assert z.is_prime == False
    assert z.is_composite is False
    assert z.is_number is True


def test_one():
    z = Integer(1)
    assert z.is_commutative == True
    assert z.is_integer == True
    assert z.is_rational == True
    assert z.is_algebraic == True
    assert z.is_transcendental is False
    assert z.is_real == True
    assert z.is_complex == True
    assert z.is_noninteger is False
    assert z.is_irrational is False
    assert z.is_imaginary == False
    assert z.is_positive == True
    assert z.is_negative == False
    assert z.is_nonpositive == False
    assert z.is_nonnegative == True
    assert z.is_even == False
    assert z.is_odd == True
    assert z.is_finite == True
    assert z.is_infinite is False
    assert z.is_comparable is True
    assert z.is_prime == False
    assert z.is_number is True
    assert z.is_composite is False  # issue 8807


def test_negativeone():
    z = Integer(-1)
    assert z.is_commutative == True
    assert z.is_integer == True
    assert z.is_rational == True
    assert z.is_algebraic == True
    assert z.is_transcendental is False
    assert z.is_real == True
    assert z.is_complex == True
    assert z.is_noninteger is False
    assert z.is_irrational is False
    assert z.is_imaginary == False
    assert z.is_positive == False
    assert z.is_negative == True
    assert z.is_nonpositive == True
    assert z.is_nonnegative == False
    assert z.is_even == False
    assert z.is_odd == True
    assert z.is_finite == True
    assert z.is_infinite is False
    assert z.is_comparable is True
    assert z.is_prime == False
    assert z.is_composite is False
    assert z.is_number is True


def test_infinity():
    oo = S.Infinity

    assert oo.is_commutative == True
    assert oo.is_integer == False
    assert oo.is_rational == False
    assert oo.is_algebraic == False
    assert oo.is_transcendental is False
    assert oo.is_extended_real == True
    assert oo.is_real == False
    assert oo.is_complex == False
    assert oo.is_noninteger is True
    assert oo.is_irrational is False
    assert oo.is_imaginary == False
    assert oo.is_nonzero == False
    assert oo.is_positive == False
    assert oo.is_negative == False
    assert oo.is_nonpositive == False
    assert oo.is_nonnegative == False
    assert oo.is_extended_nonzero == True
    assert oo.is_extended_positive == True
    assert oo.is_extended_negative == False
    assert oo.is_extended_nonpositive == False
    assert oo.is_extended_nonnegative == True
    assert oo.is_even == False
    assert oo.is_odd == False
    assert oo.is_finite == False
    assert oo.is_infinite is True
    assert oo.is_comparable is True
    assert oo.is_prime == False
    assert oo.is_composite is False
    assert oo.is_number is True


def test_neg_infinity():
    mm = S.NegativeInfinity

    assert mm.is_commutative == True
    assert mm.is_integer == False
    assert mm.is_rational == False
    assert mm.is_algebraic == False
    assert mm.is_transcendental is False
    assert mm.is_extended_real == True
    assert mm.is_real == False
    assert mm.is_complex == False
    assert mm.is_noninteger is True
    assert mm.is_irrational is False
    assert mm.is_imaginary == False
    assert mm.is_nonzero == False
    assert mm.is_positive == False
    assert mm.is_negative == False
    assert mm.is_nonpositive == False
    assert mm.is_nonnegative == False
    assert mm.is_extended_nonzero == True
    assert mm.is_extended_positive == False
    assert mm.is_extended_negative == True
    assert mm.is_extended_nonpositive == True
    assert mm.is_extended_nonnegative == False
    assert mm.is_even == False
    assert mm.is_odd == False
    assert mm.is_finite == False
    assert mm.is_infinite is True
    assert mm.is_comparable is True
    assert mm.is_prime == False
    assert mm.is_composite is False
    assert mm.is_number is True


def test_zoo():
    zoo = S.ComplexInfinity
    assert zoo.is_complex == False
    assert zoo.is_real == False
    assert zoo.is_prime == False


def test_nan():
    nan = S.NaN

    assert nan.is_commutative == True
    assert nan.is_integer is None
    assert nan.is_rational is None
    assert nan.is_algebraic is None
    assert nan.is_transcendental is None
    assert nan.is_real is None
    assert nan.is_complex is None
    assert nan.is_noninteger is None
    assert nan.is_irrational is None
    assert nan.is_imaginary is None
    assert nan.is_positive is None
    assert nan.is_negative is None
    assert nan.is_nonpositive is None
    assert nan.is_nonnegative is None
    assert nan.is_even is None
    assert nan.is_odd is None
    assert nan.is_finite is None
    assert nan.is_infinite is None
    assert nan.is_comparable is False
    assert nan.is_prime is None
    assert nan.is_composite is None
    assert nan.is_number is True


def test_pos_rational():
    r = Rational(3, 4)
    assert r.is_commutative == True
    assert r.is_integer == False
    assert r.is_rational == True
    assert r.is_algebraic == True
    assert r.is_transcendental is False
    assert r.is_real == True
    assert r.is_complex == True
    assert r.is_noninteger is True
    assert r.is_irrational is False
    assert r.is_imaginary == False
    assert r.is_positive == True
    assert r.is_negative == False
    assert r.is_nonpositive == False
    assert r.is_nonnegative == True
    assert r.is_even == False
    assert r.is_odd == False
    assert r.is_finite == True
    assert r.is_infinite is False
    assert r.is_comparable is True
    assert r.is_prime == False
    assert r.is_composite is False

    r = Rational(1, 4)
    assert r.is_nonpositive == False
    assert r.is_positive == True
    assert r.is_negative == False
    assert r.is_nonnegative == True
    r = Rational(5, 4)
    assert r.is_negative == False
    assert r.is_positive == True
    assert r.is_nonpositive == False
    assert r.is_nonnegative == True
    r = Rational(5, 3)
    assert r.is_nonnegative == True
    assert r.is_positive == True
    assert r.is_negative == False
    assert r.is_nonpositive == False


def test_neg_rational():
    r = Rational(-3, 4)
    assert r.is_positive == False
    assert r.is_nonpositive == True
    assert r.is_negative == True
    assert r.is_nonnegative == False
    r = Rational(-1, 4)
    assert r.is_nonpositive == True
    assert r.is_positive == False
    assert r.is_negative == True
    assert r.is_nonnegative == False
    r = Rational(-5, 4)
    assert r.is_negative == True
    assert r.is_positive == False
    assert r.is_nonpositive == True
    assert r.is_nonnegative == False
    r = Rational(-5, 3)
    assert r.is_nonnegative == False
    assert r.is_positive == False
    assert r.is_negative == True
    assert r.is_nonpositive == True


def test_pi():
    z = S.Pi
    assert z.is_commutative == True
    assert z.is_integer == False
    assert z.is_rational == False
    assert z.is_algebraic == False
    assert z.is_transcendental is True
    assert z.is_real == True
    assert z.is_complex == True
    assert z.is_noninteger is True
    assert z.is_irrational is True
    assert z.is_imaginary == False
    assert z.is_positive == True
    assert z.is_negative == False
    assert z.is_nonpositive == False
    assert z.is_nonnegative == True
    assert z.is_even == False
    assert z.is_odd == False
    assert z.is_finite == True
    assert z.is_infinite is False
    assert z.is_comparable is True
    assert z.is_prime == False
    assert z.is_composite is False


def test_E():
    z = S.Exp1
    assert z.is_commutative == True
    assert z.is_integer == False
    assert z.is_rational == False
    assert z.is_algebraic == False
    assert z.is_transcendental is True
    assert z.is_real == True
    assert z.is_complex == True
    assert z.is_noninteger is True
    assert z.is_irrational is True
    assert z.is_imaginary == False
    assert z.is_positive == True
    assert z.is_negative == False
    assert z.is_nonpositive == False
    assert z.is_nonnegative == True
    assert z.is_even == False
    assert z.is_odd == False
    assert z.is_finite == True
    assert z.is_infinite is False
    assert z.is_comparable is True
    assert z.is_prime == False
    assert z.is_composite is False


def test_I():
    z = S.ImaginaryUnit
    assert z.is_commutative == True
    assert z.is_integer == False
    assert z.is_rational == False
    assert z.is_algebraic == True
    assert z.is_transcendental is False
    assert z.is_real == False
    assert z.is_complex == True
    assert z.is_noninteger is False
    assert z.is_irrational is False
    assert z.is_imaginary == True
    assert z.is_positive == False
    assert z.is_negative == False
    assert z.is_nonpositive == False
    assert z.is_nonnegative == False
    assert z.is_even == False
    assert z.is_odd == False
    assert z.is_finite == True
    assert z.is_infinite is False
    assert z.is_comparable is False
    assert z.is_prime == False
    assert z.is_composite is False


def test_symbol_real_false():
    # issue 3848
    a = Symbol('a', real=False)

    assert a.is_real == False
    assert a.is_integer == False
    assert a.is_zero == False

    assert a.is_negative == False
    assert a.is_positive == False
    assert a.is_nonnegative == False
    assert a.is_nonpositive == False
    assert a.is_nonzero == False

    assert a.is_extended_negative is None
    assert a.is_extended_positive is None
    assert a.is_extended_nonnegative is None
    assert a.is_extended_nonpositive is None
    assert a.is_extended_nonzero is None


def test_symbol_extended_real_false():
    # issue 3848
    a = Symbol('a', extended_real=False)

    assert a.is_real == False
    assert a.is_integer == False
    assert a.is_zero == False

    assert a.is_negative == False
    assert a.is_positive == False
    assert a.is_nonnegative == False
    assert a.is_nonpositive == False
    assert a.is_nonzero == False

    assert a.is_extended_negative == False
    assert a.is_extended_positive == False
    assert a.is_extended_nonnegative == False
    assert a.is_extended_nonpositive == False
    assert a.is_extended_nonzero == False


def test_symbol_imaginary():
    a = Symbol('a', imaginary=True)

    assert a.is_real == False
    assert a.is_integer == False
    assert a.is_negative == False
    assert a.is_positive == False
    assert a.is_nonnegative == False
    assert a.is_nonpositive == False
    assert a.is_zero == False
    assert a.is_nonzero == False  # since nonzero -> real


def test_symbol_zero():
    x = Symbol('x', zero=True)
    assert x.is_positive == False
    assert x.is_nonpositive
    assert x.is_negative == False
    assert x.is_nonnegative
    assert x.is_zero == True
    # TODO Change to x.is_nonzero is None
    # See https://github.com/sympy/sympy/pull/9583
    assert x.is_nonzero == False
    assert x.is_finite == True


def test_symbol_positive():
    x = Symbol('x', positive=True)
    assert x.is_positive == True
    assert x.is_nonpositive == False
    assert x.is_negative == False
    assert x.is_nonnegative == True
    assert x.is_zero == False
    assert x.is_nonzero == True


def test_neg_symbol_positive():
    x = -Symbol('x', positive=True)
    assert x.is_positive == False
    assert x.is_nonpositive == True
    assert x.is_negative == True
    assert x.is_nonnegative == False
    assert x.is_zero == False
    assert x.is_nonzero == True


def test_symbol_nonpositive():
    x = Symbol('x', nonpositive=True)
    assert x.is_positive == False
    assert x.is_nonpositive == True
    assert x.is_negative is None
    assert x.is_nonnegative is None
    assert x.is_zero is None
    assert x.is_nonzero is None


def test_neg_symbol_nonpositive():
    x = -Symbol('x', nonpositive=True)
    assert x.is_positive is None
    assert x.is_nonpositive is None
    assert x.is_negative == False
    assert x.is_nonnegative == True
    assert x.is_zero is None
    assert x.is_nonzero is None


def test_symbol_falsepositive():
    x = Symbol('x', positive=False)
    assert x.is_positive == False
    assert x.is_nonpositive is None
    assert x.is_negative is None
    assert x.is_nonnegative is None
    assert x.is_zero is None
    assert x.is_nonzero is None


def test_symbol_falsepositive_mul():
    # To test pull request 9379
    # Explicit handling of arg.is_positive=False was added to Mul._eval_is_positive
    x = 2*Symbol('x', positive=False)
    assert x.is_positive == False  # This was None before
    assert x.is_nonpositive is None
    assert x.is_negative is None
    assert x.is_nonnegative is None
    assert x.is_zero is None
    assert x.is_nonzero is None


@XFAIL
def test_symbol_infinitereal_mul():
    ix = Symbol('ix', infinite=True, extended_real=True)
    assert (-ix).is_extended_positive is None


def test_neg_symbol_falsepositive():
    x = -Symbol('x', positive=False)
    assert x.is_positive is None
    assert x.is_nonpositive is None
    assert x.is_negative == False
    assert x.is_nonnegative is None
    assert x.is_zero is None
    assert x.is_nonzero is None


def test_neg_symbol_falsenegative():
    # To test pull request 9379
    # Explicit handling of arg.is_negative=False was added to Mul._eval_is_positive
    x = -Symbol('x', negative=False)
    assert x.is_positive == False  # This was None before
    assert x.is_nonpositive is None
    assert x.is_negative is None
    assert x.is_nonnegative is None
    assert x.is_zero is None
    assert x.is_nonzero is None


def test_symbol_falsepositive_real():
    x = Symbol('x', positive=False, real=True)
    assert x.is_positive == False
    assert x.is_nonpositive == True
    assert x.is_negative is None
    assert x.is_nonnegative is None
    assert x.is_zero is None
    assert x.is_nonzero is None


def test_neg_symbol_falsepositive_real():
    x = -Symbol('x', positive=False, real=True)
    assert x.is_positive is None
    assert x.is_nonpositive is None
    assert x.is_negative == False
    assert x.is_nonnegative == True
    assert x.is_zero is None
    assert x.is_nonzero is None


def test_symbol_falsenonnegative():
    x = Symbol('x', nonnegative=False)
    assert x.is_positive == False
    assert x.is_nonpositive is None
    assert x.is_negative is None
    assert x.is_nonnegative == False
    assert x.is_zero == False
    assert x.is_nonzero is None


@XFAIL
def test_neg_symbol_falsenonnegative():
    x = -Symbol('x', nonnegative=False)
    assert x.is_positive is None
    assert x.is_nonpositive == False  # this currently returns None
    assert x.is_negative == False  # this currently returns None
    assert x.is_nonnegative is None
    assert x.is_zero == False  # this currently returns None
    assert x.is_nonzero == True  # this currently returns None


def test_symbol_falsenonnegative_real():
    x = Symbol('x', nonnegative=False, real=True)
    assert x.is_positive == False
    assert x.is_nonpositive == True
    assert x.is_negative == True
    assert x.is_nonnegative == False
    assert x.is_zero == False
    assert x.is_nonzero == True


def test_neg_symbol_falsenonnegative_real():
    x = -Symbol('x', nonnegative=False, real=True)
    assert x.is_positive == True
    assert x.is_nonpositive == False
    assert x.is_negative == False
    assert x.is_nonnegative == True
    assert x.is_zero == False
    assert x.is_nonzero == True


def test_prime():
    assert S.NegativeOne.is_prime == False
    assert S(-2).is_prime == False
    assert S(-4).is_prime == False
    assert S.Zero.is_prime == False
    assert S.One.is_prime == False
    assert S(2).is_prime == True
    assert S(17).is_prime == True
    assert S(4).is_prime == False


def test_composite():
    assert S.NegativeOne.is_composite is False
    assert S(-2).is_composite is False
    assert S(-4).is_composite is False
    assert S.Zero.is_composite is False
    assert S(2).is_composite is False
    assert S(17).is_composite is False
    assert S(4).is_composite is True
    x = Dummy(integer=True, positive=True, prime=False)
    assert x.is_composite is None # x could be 1
    assert (x + 1).is_composite is None
    x = Dummy(positive=True, even=True, prime=False)
    assert x.is_integer == True
    assert x.is_composite is True


def test_prime_symbol():
    x = Symbol('x', prime=True)
    assert x.is_prime == True
    assert x.is_integer == True
    assert x.is_positive == True
    assert x.is_negative == False
    assert x.is_nonpositive == False
    assert x.is_nonnegative == True

    x = Symbol('x', prime=False)
    assert x.is_prime == False
    assert x.is_integer is None
    assert x.is_positive is None
    assert x.is_negative is None
    assert x.is_nonpositive is None
    assert x.is_nonnegative is None


def test_symbol_noncommutative():
    x = Symbol('x', commutative=True)
    assert x.is_complex is None

    x = Symbol('x', commutative=False)
    assert x.is_integer == False
    assert x.is_rational == False
    assert x.is_algebraic == False
    assert x.is_irrational is False
    assert x.is_real == False
    assert x.is_complex == False


def test_other_symbol():
    x = Symbol('x', integer=True)
    assert x.is_integer == True
    assert x.is_real == True
    assert x.is_finite == True

    x = Symbol('x', integer=True, nonnegative=True)
    assert x.is_integer == True
    assert x.is_nonnegative == True
    assert x.is_negative == False
    assert x.is_positive is None
    assert x.is_finite == True

    x = Symbol('x', integer=True, nonpositive=True)
    assert x.is_integer == True
    assert x.is_nonpositive == True
    assert x.is_positive == False
    assert x.is_negative is None
    assert x.is_finite == True

    x = Symbol('x', odd=True)
    assert x.is_odd == True
    assert x.is_even == False
    assert x.is_integer == True
    assert x.is_finite == True

    x = Symbol('x', odd=False)
    assert x.is_odd == False
    assert x.is_even is None
    assert x.is_integer is None
    assert x.is_finite is None

    x = Symbol('x', even=True)
    assert x.is_even == True
    assert x.is_odd == False
    assert x.is_integer == True
    assert x.is_finite == True

    x = Symbol('x', even=False)
    assert x.is_even == False
    assert x.is_odd is None
    assert x.is_integer is None
    assert x.is_finite is None

    x = Symbol('x', integer=True, nonnegative=True)
    assert x.is_integer == True
    assert x.is_nonnegative == True
    assert x.is_finite == True

    x = Symbol('x', integer=True, nonpositive=True)
    assert x.is_integer == True
    assert x.is_nonpositive == True
    assert x.is_finite == True

    x = Symbol('x', rational=True)
    assert x.is_real == True
    assert x.is_finite == True

    x = Symbol('x', rational=False)
    assert x.is_real is None
    assert x.is_finite is None

    x = Symbol('x', irrational=True)
    assert x.is_real == True
    assert x.is_finite == True

    x = Symbol('x', irrational=False)
    assert x.is_real is None
    assert x.is_finite is None

    with raises(AttributeError):
        x.is_real = False

    x = Symbol('x', algebraic=True)
    assert x.is_transcendental is False
    x = Symbol('x', transcendental=True)
    assert x.is_algebraic == False
    assert x.is_rational == False
    assert x.is_integer == False


def test_issue_3825():
    """catch: hash instability"""
    x = Symbol("x")
    y = Symbol("y")
    a1 = x + y
    a2 = y + x
    a2.is_comparable

    h1 = hash(a1)
    h2 = hash(a2)
    assert h1 == h2


def test_issue_4822():
    z = (-1)**Rational(1, 3)*(1 - I*sqrt(3))
    assert z.is_real in [True, None]


def test_hash_vs_typeinfo():
    """seemingly different typeinfo, but in fact equal"""

    # the following two are semantically equal
    x1 = Symbol('x', even=True)
    x2 = Symbol('x', integer=True, odd=False)

    assert hash(x1) == hash(x2)
    assert x1 == x2


def test_hash_vs_typeinfo_2():
    """different typeinfo should mean !eq"""
    # the following two are semantically different
    x = Symbol('x')
    x1 = Symbol('x', even=True)

    assert x != x1
    assert hash(x) != hash(x1)  # This might fail with very low probability


def test_hash_vs_eq():
    """catch: different hash for equal objects"""
    a = 1 + S.Pi    # important: do not fold it into a Number instance
    ha = hash(a)  # it should be Add/Mul/... to trigger the bug

    a.is_positive   # this uses .evalf() and deduces it is positive
    assert a.is_positive == True

    # be sure that hash stayed the same
    assert ha == hash(a)

    # now b should be the same expression
    b = a.expand(trig=True)
    hb = hash(b)

    assert a == b
    assert ha == hb


def test_Add_is_pos_neg():
    # these cover lines not covered by the rest of tests in core
    n = Symbol('n', extended_negative=True, infinite=True)
    nn = Symbol('n', extended_nonnegative=True, infinite=True)
    np = Symbol('n', extended_nonpositive=True, infinite=True)
    p = Symbol('p', extended_positive=True, infinite=True)
    r = Dummy(extended_real=True, finite=False)
    x = Symbol('x')
    xf = Symbol('xf', finite=True)
    assert (n + p).is_extended_positive is None
    assert (n + x).is_extended_positive is None
    assert (p + x).is_extended_positive is None
    assert (n + p).is_extended_negative is None
    assert (n + x).is_extended_negative is None
    assert (p + x).is_extended_negative is None

    assert (n + xf).is_extended_positive == False
    assert (p + xf).is_extended_positive == True
    assert (n + xf).is_extended_negative == True
    assert (p + xf).is_extended_negative == False

    assert (x - S.Infinity).is_extended_negative is None  # issue 7798
    # issue 8046, 16.2
    assert (p + nn).is_extended_positive
    assert (n + np).is_extended_negative
    assert (p + r).is_extended_positive is None


def test_Add_is_imaginary():
    nn = Dummy(nonnegative=True)
    assert (I*nn + I).is_imaginary  # issue 8046, 17


def test_Add_is_algebraic():
    a = Symbol('a', algebraic=True)
    b = Symbol('a', algebraic=True)
    na = Symbol('na', algebraic=False)
    nb = Symbol('nb', algebraic=False)
    x = Symbol('x')
    assert (a + b).is_algebraic
    assert (na + nb).is_algebraic is None
    assert (a + na).is_algebraic == False
    assert (a + x).is_algebraic is None
    assert (na + x).is_algebraic is None


def test_Mul_is_algebraic():
    a = Symbol('a', algebraic=True)
    b = Symbol('b', algebraic=True)
    na = Symbol('na', algebraic=False)
    an = Symbol('an', algebraic=True, nonzero=True)
    nb = Symbol('nb', algebraic=False)
    x = Symbol('x')
    assert (a*b).is_algebraic == True
    assert (na*nb).is_algebraic is None
    assert (a*na).is_algebraic is None
    assert (an*na).is_algebraic == False
    assert (a*x).is_algebraic is None
    assert (na*x).is_algebraic is None


def test_Pow_is_algebraic():
    e = Symbol('e', algebraic=True)

    assert Pow(1, e, evaluate=False).is_algebraic
    assert Pow(0, e, evaluate=False).is_algebraic

    a = Symbol('a', algebraic=True)
    azf = Symbol('azf', algebraic=True, zero=False)
    na = Symbol('na', algebraic=False)
    ia = Symbol('ia', algebraic=True, irrational=True)
    ib = Symbol('ib', algebraic=True, irrational=True)
    r = Symbol('r', rational=True)
    x = Symbol('x')
    assert (a**2).is_algebraic == True
    assert (a**r).is_algebraic is None
    assert (azf**r).is_algebraic == True
    assert (a**x).is_algebraic is None
    assert (na**r).is_algebraic is None
    assert (ia**r).is_algebraic == True
    assert (ia**ib).is_algebraic == False

    assert (a**e).is_algebraic is None

    # Gelfond-Schneider constant:
    assert Pow(2, sqrt(2), evaluate=False).is_algebraic == False

    assert Pow(S.GoldenRatio, sqrt(3), evaluate=False).is_algebraic == False

    # issue 8649
    t = Symbol('t', real=True, transcendental=True)
    n = Symbol('n', integer=True)
    assert (t**n).is_algebraic is None
    assert (t**n).is_integer is None

    assert (pi**3).is_algebraic == False
    r = Symbol('r', zero=True)
    assert (pi**r).is_algebraic == True


def test_Mul_is_prime_composite():
    x = Symbol('x', positive=True, integer=True)
    y = Symbol('y', positive=True, integer=True)
    assert (x*y).is_prime is None
    assert ( (x+1)*(y+1) ).is_prime == False
    assert ( (x+1)*(y+1) ).is_composite is True

    x = Symbol('x', positive=True)
    assert ( (x+1)*(y+1) ).is_prime is None
    assert ( (x+1)*(y+1) ).is_composite is None


def test_Pow_is_pos_neg():
    z = Symbol('z', real=True)
    w = Symbol('w', nonpositive=True)

    assert (S.NegativeOne**S(2)).is_positive == True
    assert (S.One**z).is_positive == True
    assert (S.NegativeOne**S(3)).is_positive == False
    assert (S.Zero**S.Zero).is_positive == True  # 0**0 is 1
    assert (w**S(3)).is_positive == False
    assert (w**S(2)).is_positive is None
    assert (I**2).is_positive == False
    assert (I**4).is_positive == True

    # tests emerging from #16332 issue
    p = Symbol('p', zero=True)
    q = Symbol('q', zero=False, real=True)
    j = Symbol('j', zero=False, even=True)
    x = Symbol('x', zero=True)
    y = Symbol('y', zero=True)
    assert (p**q).is_positive == False
    assert (p**q).is_negative == False
    assert (p**j).is_positive == False
    assert (x**y).is_positive == True   # 0**0
    assert (x**y).is_negative == False


def test_Pow_is_prime_composite():
    x = Symbol('x', positive=True, integer=True)
    y = Symbol('y', positive=True, integer=True)
    assert (x**y).is_prime is None
    assert ( x**(y+1) ).is_prime == False
    assert ( x**(y+1) ).is_composite is None
    assert ( (x+1)**(y+1) ).is_composite is True
    assert ( (-x-1)**(2*y) ).is_composite is True

    x = Symbol('x', positive=True)
    assert (x**y).is_prime is None


def test_Mul_is_infinite():
    x = Symbol('x')
    f = Symbol('f', finite=True)
    i = Symbol('i', infinite=True)
    z = Dummy(zero=True)
    nzf = Dummy(finite=True, zero=False)
    from sympy import Mul
    assert (x*f).is_finite is None
    assert (x*i).is_finite is None
    assert (f*i).is_finite is None
    assert (x*f*i).is_finite is None
    assert (z*i).is_finite is None
    assert (nzf*i).is_finite == False
    assert (z*f).is_finite == True
    assert Mul(0, f, evaluate=False).is_finite == True
    assert Mul(0, i, evaluate=False).is_finite is None

    assert (x*f).is_infinite is None
    assert (x*i).is_infinite is None
    assert (f*i).is_infinite is None
    assert (x*f*i).is_infinite is None
    assert (z*i).is_infinite is S.NaN.is_infinite
    assert (nzf*i).is_infinite is True
    assert (z*f).is_infinite is False
    assert Mul(0, f, evaluate=False).is_infinite is False
    assert Mul(0, i, evaluate=False).is_infinite is S.NaN.is_infinite


def test_Add_is_infinite():
    x = Symbol('x')
    f = Symbol('f', finite=True)
    i = Symbol('i', infinite=True)
    i2 = Symbol('i2', infinite=True)
    z = Dummy(zero=True)
    nzf = Dummy(finite=True, zero=False)
    from sympy import Add
    assert (x+f).is_finite is None
    assert (x+i).is_finite is None
    assert (f+i).is_finite == False
    assert (x+f+i).is_finite is None
    assert (z+i).is_finite == False
    assert (nzf+i).is_finite == False
    assert (z+f).is_finite == True
    assert (i+i2).is_finite is None
    assert Add(0, f, evaluate=False).is_finite == True
    assert Add(0, i, evaluate=False).is_finite == False

    assert (x+f).is_infinite is None
    assert (x+i).is_infinite is None
    assert (f+i).is_infinite is True
    assert (x+f+i).is_infinite is None
    assert (z+i).is_infinite is True
    assert (nzf+i).is_infinite is True
    assert (z+f).is_infinite is False
    assert (i+i2).is_infinite is None
    assert Add(0, f, evaluate=False).is_infinite is False
    assert Add(0, i, evaluate=False).is_infinite is True


def test_special_is_rational():
    i = Symbol('i', integer=True)
    i2 = Symbol('i2', integer=True)
    ni = Symbol('ni', integer=True, nonzero=True)
    r = Symbol('r', rational=True)
    rn = Symbol('r', rational=True, nonzero=True)
    nr = Symbol('nr', irrational=True)
    x = Symbol('x')
    assert sqrt(3).is_rational == False
    assert (3 + sqrt(3)).is_rational == False
    assert (3*sqrt(3)).is_rational == False
    assert exp(3).is_rational == False
    assert exp(ni).is_rational == False
    assert exp(rn).is_rational == False
    assert exp(x).is_rational is None
    assert exp(log(3), evaluate=False).is_rational == True
    assert log(exp(3), evaluate=False).is_rational == True
    assert log(3).is_rational == False
    assert log(ni + 1).is_rational == False
    assert log(rn + 1).is_rational == False
    assert log(x).is_rational is None
    assert (sqrt(3) + sqrt(5)).is_rational is None
    assert (sqrt(3) + S.Pi).is_rational == False
    assert (x**i).is_rational is None
    assert (i**i).is_rational == True
    assert (i**i2).is_rational is None
    assert (r**i).is_rational is None
    assert (r**r).is_rational is None
    assert (r**x).is_rational is None
    assert (nr**i).is_rational is None  # issue 8598
    assert (nr**Symbol('z', zero=True)).is_rational
    assert sin(1).is_rational == False
    assert sin(ni).is_rational == False
    assert sin(rn).is_rational == False
    assert sin(x).is_rational is None
    assert asin(r).is_rational == False
    assert sin(asin(3), evaluate=False).is_rational == True


@XFAIL
def test_issue_6275():
    x = Symbol('x')
    # both zero or both Muls...but neither "change would be very appreciated.
    # This is similar to x/x => 1 even though if x = 0, it is really nan.
    assert isinstance(x*0, type(0*S.Infinity))
    if 0*S.Infinity is S.NaN:
        b = Symbol('b', finite=None)
        assert (b*0).is_zero is None


def test_sanitize_assumptions():
    # issue 6666
    for cls in (Symbol, Dummy, Wild):
        x = cls('x', real=1, positive=0)
        assert x.is_real == True
        assert x.is_positive == False
        assert cls('', real=True, positive=None).is_positive is None
        raises(ValueError, lambda: cls('', commutative=None))
    raises(ValueError, lambda: Symbol._sanitize(dict(commutative=None)))


def test_special_assumptions():
    e = -3 - sqrt(5) + (-sqrt(10)/2 - sqrt(2)/2)**2
    assert simplify(e < 0) is S.false
    assert simplify(e > 0) is S.false
    assert (e == 0) is False  # it's not a literal 0
    assert e.equals(0) is True


def test_inconsistent():
    # cf. issues 5795 and 5545
    raises(InconsistentAssumptions, lambda: Symbol('x', real=True,
           commutative=False))


def test_issue_6631():
    assert ((-1)**(I)).is_real == True
    assert ((-1)**(I*2)).is_real == True
    assert ((-1)**(I/2)).is_real == True
    assert ((-1)**(I*S.Pi)).is_real == True
    assert (I**(I + 2)).is_real == True


def test_issue_2730():
    assert (1/(1 + I)).is_real == False


def test_issue_4149():
    assert (3 + I).is_complex
    assert (3 + I).is_imaginary == False
    assert (3*I + S.Pi*I).is_imaginary
    # as Zero.is_imaginary == False, see issue 7649
    y = Symbol('y', real=True)
    assert (3*I + S.Pi*I + y*I).is_imaginary is None
    p = Symbol('p', positive=True)
    assert (3*I + S.Pi*I + p*I).is_imaginary
    n = Symbol('n', negative=True)
    assert (-3*I - S.Pi*I + n*I).is_imaginary

    i = Symbol('i', imaginary=True)
    assert ([(i**a).is_imaginary for a in range(4)] ==
            [False, True, False, True])

    # tests from the PR #7887:
    e = S("-sqrt(3)*I/2 + 0.866025403784439*I")
    assert e.is_real == False
    assert e.is_imaginary


def test_issue_2920():
    n = Symbol('n', negative=True)
    assert sqrt(n).is_imaginary


def test_issue_7899():
    x = Symbol('x', real=True)
    assert (I*x).is_real is None
    assert ((x - I)*(x - 1)).is_zero is None
    assert ((x - I)*(x - 1)).is_real is None


@XFAIL
def test_issue_7993():
    x = Dummy(integer=True)
    y = Dummy(noninteger=True)
    assert (x - y).is_zero == False


def test_issue_8075():
    raises(InconsistentAssumptions, lambda: Dummy(zero=True, finite=False))
    raises(InconsistentAssumptions, lambda: Dummy(zero=True, infinite=True))


def test_issue_8642():
    x = Symbol('x', real=True, integer=False)
    assert (x*2).is_integer is None, (x*2).is_integer


def test_issues_8632_8633_8638_8675_8992():
    p = Dummy(integer=True, positive=True)
    nn = Dummy(integer=True, nonnegative=True)
    assert (p - S.Half).is_positive
    assert (p - 1).is_nonnegative
    assert (nn + 1).is_positive
    assert (-p + 1).is_nonpositive
    assert (-nn - 1).is_negative
    prime = Dummy(prime=True)
    assert (prime - 2).is_nonnegative
    assert (prime - 3).is_nonnegative is None
    even = Dummy(positive=True, even=True)
    assert (even - 2).is_nonnegative

    p = Dummy(positive=True)
    assert (p/(p + 1) - 1).is_negative
    assert ((p + 2)**3 - S.Half).is_positive
    n = Dummy(negative=True)
    assert (n - 3).is_nonpositive


def test_issue_9115_9150():
    n = Dummy('n', integer=True, nonnegative=True)
    assert (factorial(n) >= 1) == True
    assert (factorial(n) < 1) == False

    assert factorial(n + 1).is_even is None
    assert factorial(n + 2).is_even == True
    assert factorial(n + 2) >= 2


def test_issue_9165():
    z = Symbol('z', zero=True)
    f = Symbol('f', finite=False)
    assert 0/z is S.NaN
    assert 0*(1/z) is S.NaN
    assert 0*f is S.NaN


def test_issue_10024():
    x = Dummy('x')
    assert Mod(x, 2*pi).is_zero is None


def test_issue_10302():
    x = Symbol('x')
    r = Symbol('r', real=True)
    u = -(3*2**pi)**(1/pi) + 2*3**(1/pi)
    i = u + u*I
    assert i.is_real is None  # w/o simplification this should fail
    assert (u + i).is_zero is None
    assert (1 + i).is_zero == False
    a = Dummy('a', zero=True)
    assert (a + I).is_zero == False
    assert (a + r*I).is_zero is None
    assert (a + I).is_imaginary
    assert (a + x + I).is_imaginary is None
    assert (a + r*I + I).is_imaginary is None


def test_complex_reciprocal_imaginary():
    assert (1 / (4 + 3*I)).is_imaginary == False


def test_issue_16313():
    x = Symbol('x', extended_real=False)
    k = Symbol('k', real=True)
    l = Symbol('l', real=True, zero=False)
    assert (-x).is_real == False
    assert (k*x).is_real is None  # k can be zero also
    assert (l*x).is_real == False
    assert (l*x*x).is_real is None  # since x*x can be a real number
    assert (-x).is_positive == False


def test_issue_16579():
    # extended_real -> finite | infinite
    x = Symbol('x', extended_real=True, infinite=False)
    y = Symbol('y', extended_real=True, finite=False)
    assert x.is_finite == True
    assert y.is_infinite is True

    # With PR 16978, complex now implies finite
    c = Symbol('c', complex=True)
    assert c.is_finite == True
    raises(InconsistentAssumptions, lambda: Dummy(complex=True, finite=False))

    # Now infinite == !finite
    nf = Symbol('nf', finite=False)
    assert nf.is_infinite is True


def test_issue_17556():
    z = I*oo
    assert z.is_imaginary == False
    assert z.is_finite == False


def test_assumptions_copy():
    assert assumptions(Symbol('x'), dict(commutative=True)
        ) == {'commutative': True}
    assert assumptions(Symbol('x'), ['integer']) == {}
    assert assumptions(Symbol('x'), ['commutative']
        ) == {'commutative': True}
    assert assumptions(Symbol('x')) == {'commutative': True}
    assert assumptions(1)['positive']
    assert assumptions(3 + I) == {
        'algebraic': True,
        'commutative': True,
        'complex': True,
        'composite': False,
        'even': False,
        'extended_negative': False,
        'extended_nonnegative': False,
        'extended_nonpositive': False,
        'extended_nonzero': False,
        'extended_positive': False,
        'extended_real': False,
        'finite': True,
        'imaginary': False,
        'infinite': False,
        'integer': False,
        'irrational': False,
        'negative': False,
        'noninteger': False,
        'nonnegative': False,
        'nonpositive': False,
        'nonzero': False,
        'odd': False,
        'positive': False,
        'prime': False,
        'rational': False,
        'real': False,
        'transcendental': False,
        'zero': False}


def test_check_assumptions():
    x = Symbol('x', positive=True)
    assert check_assumptions(1, x) is True
    assert check_assumptions(1, 1) is True
    assert check_assumptions(-1, 1) is False
    i = Symbol('i', integer=True)
    # don't know if i is positive (or prime, etc...)
    assert check_assumptions(i, 1) is None
    assert check_assumptions(Dummy(integer=None), integer=True) is None
    assert check_assumptions(Dummy(integer=None), integer=False) is None
    assert check_assumptions(Dummy(integer=False), integer=True) is False
    assert check_assumptions(Dummy(integer=True), integer=False) is False
    # no T/F assumptions to check
    assert check_assumptions(Dummy(integer=False), integer=None) is True
    raises(ValueError, lambda: check_assumptions(2*x, x, positive=True))


def test_failing_assumptions():
    x = Symbol('x', real=True, positive=True)
    y = Symbol('y')
    assert failing_assumptions(6*x + y, **x.assumptions0) == \
    {'real': None, 'imaginary': None, 'complex': None, 'hermitian': None,
    'positive': None, 'nonpositive': None, 'nonnegative': None, 'nonzero': None,
    'negative': None, 'zero': None, 'extended_real': None, 'finite': None,
    'infinite': None, 'extended_negative': None, 'extended_nonnegative': None,
    'extended_nonpositive': None, 'extended_nonzero': None,
    'extended_positive': None }


def test_common_assumptions():
    assert common_assumptions([0, 1, 2]
        ) == {'algebraic': True, 'irrational': False, 'hermitian':
        True, 'extended_real': True, 'real': True, 'extended_negative':
        False, 'extended_nonnegative': True, 'integer': True,
        'rational': True, 'imaginary': False, 'complex': True,
        'commutative': True,'noninteger': False, 'composite': False,
        'infinite': False, 'nonnegative': True, 'finite': True,
        'transcendental': False,'negative': False}
    assert common_assumptions([0, 1, 2], 'positive integer'.split()
        ) == {'integer': True}
    assert common_assumptions([0, 1, 2], []) == {}
    assert common_assumptions([], ['integer']) == {}
    assert common_assumptions([0], ['integer']) == {'integer': True}
