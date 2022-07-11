"""Finite extensions of ring domains."""

from sympy.polys.polyerrors import CoercionFailed
from sympy.polys.polytools import Poly

class ExtensionElement(object):
    """
    Element of a finite extension.

    A class of univariate polynomials modulo the ``modulus``
    of the extension ``ext``. It is represented by the
    unique polynomial ``rep`` of lowest degree. Both
    ``rep`` and the representation ``mod`` of ``modulus``
    are of class DMP.

    """
    __slots__ = ['rep', 'ext']

    def __init__(self, rep, ext):
        self.rep = rep
        self.ext = ext

    def __neg__(f):
        return ExtElem(-f.rep, f.ext)

    def _get_rep(f, g):
        if isinstance(g, ExtElem):
            if g.ext == f.ext:
                return g.rep
            else:
                return None
        else:
            try:
                g = f.ext.convert(g)
                return g.rep
            except CoercionFailed:
                return None

    def __add__(f, g):
        rep = f._get_rep(g)
        if rep is not None:
            return ExtElem(f.rep + rep, f.ext)
        else:
            return NotImplemented

    __radd__ = __add__

    def __sub__(f, g):
        rep = f._get_rep(g)
        if rep is not None:
            return ExtElem(f.rep - rep, f.ext)
        else:
            return NotImplemented

    def __rsub__(f, g):
        rep = f._get_rep(g)
        if rep is not None:
            return ExtElem(rep - f.rep, f.ext)
        else:
            return NotImplemented

    def __mul__(f, g):
        rep = f._get_rep(g)
        if rep is not None:
            return ExtElem((f.rep*rep) % f.ext.mod, f.ext)
        else:
            return NotImplemented

    __rmul__ = __mul__

    def __pow__(f, n):
        if not isinstance(n, int):
            raise TypeError("exponent of type 'int' expected")
        if n < 0:
            raise ValueError("negative powers are not defined")

        b = f.rep
        m = f.ext.mod
        r = f.ext.one.rep
        while n > 0:
            if n % 2:
                r = (r*b) % m
            b = (b*b) % m
            n //= 2

        return ExtElem(r, f.ext)

    def __eq__(f, g):
        if isinstance(g, ExtElem):
            return f.rep == g.rep and f.ext == g.ext
        else:
            return NotImplemented

    def __ne__(f, g):
        return not f == g

    def __hash__(f):
        return hash((f.rep, f.ext))

    def __str__(f):
        from sympy.printing.str import sstr
        return sstr(f.rep)

    __repr__ = __str__

ExtElem = ExtensionElement


class MonogenicFiniteExtension(object):
    """
    Finite extension generated by an integral element.

    The generator is defined by a monic univariate
    polynomial derived from the argument ``mod``.

    """
    def __init__(self, mod):
        if not (isinstance(mod, Poly) and mod.is_univariate):
            raise TypeError("modulus must be a univariate Poly")

        mod, rem = mod.div(mod.LC())
        if not rem.is_zero:
            raise ValueError("modulus could not be made monic")

        self.rank = mod.degree()
        self.modulus = mod
        self.mod = mod.rep  # DMP representation

        self.domain = dom = mod.domain
        self.ring = mod.rep.ring or dom.old_poly_ring(*mod.gens)

        self.zero = self.convert(self.ring.zero)
        self.one = self.convert(self.ring.one)

        gen = self.ring.gens[0]
        self.generator = self.convert(gen)
        self.basis = tuple(self.convert(gen**i)
                      for i in range(self.rank))

    def convert(self, f):
        rep = self.ring.convert(f)
        return ExtElem(rep % self.mod, self)

    __call__ = convert

    def __str__(self):
        return "%s/(%s)" % (self.ring, self.modulus.as_expr())

    __repr__ = __str__

FiniteExtension = MonogenicFiniteExtension
