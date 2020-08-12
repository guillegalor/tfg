from sage.coding.linear_code import (AbstractLinearCode)
from sage.coding.encoder import Encoder
from sage.coding.decoder import Decoder
from copy import copy
from sage.rings.integer import Integer
from sage.modules.free_module_element import vector
from sage.matrix.constructor import matrix

def right_extended_euclidean_algorithm(f, g):
    '''
    Implementation of the right extended euclidean algorithm.

    INPUT:
    - ``f`` -- one skew polynomial.
    - ``g`` -- another skew polynomial.

    OUTPUT:
    - ``(n, (u, v, r))`` --  with u, v, r arrays of skew polynomials
    such that f*u[i] + g*v[i] = r[i] for all 0 <= i <= n
    '''
    # Initialization
    u = [1, 0]
    v = [0, 1]
    r = [f, g]

    i = 1
    while r[i] != 0:
        q, rem = r[i-1].left_quo_rem(r[i])
        u.append(u[i-1] - u[i]*q)
        v.append(v[i-1] - v[i]*q)
        r.append(rem)

        i = i+1
    return (i, (u, v, r))

class SkewCyclicCode(AbstractLinearCode):
    r"""
    ...
    TODO
    ...
    """

    _registered_encoders = {}
    _registered_decoders = {}

    def __init__(self, generator_pol=None):
        r"""
        TESTS:

        We check that the length of the code (order of the twisted map) is bigger
        than the degree of the polynomial::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
            Traceback (most recent call last):
            ...
            ValueError:

        And we check that the generator polynomial divides `x^{n} - 1`,
        where `n` is the length of the code::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
            Traceback (most recent call last):
            ...
            ValueError:
        """
        if (generator_pol is not None and length is not None):
            F = generator_pol.base_ring()
            R = generator_pol.parent()
            length = R.twist_map()
            deg = generator_pol.degree()
            if not generator_pol.right_divides(R.gen() ** length - 1):
                raise ValueError("Provided polynomial must divide x^n - 1, "
                                 "where n is the provided length.")
            self._skew_polynomial_ring = R
            self._dimension = length - deg
            if not generator_pol.is_monic():
                self._generator_polynomial = generator_pol.right_monic()
            else:
                self._generator_polynomial = generator_pol

            # TODO Add proper enconder and decoder
            super(SkewCyclicCode, self).__init__(F, length, "Vector", "Syndrome")

        else:
            raise AttributeError("You must provide either a code, or a list "
                                 "of powers and the length and the field, or "
                                 "a generator polynomial and the code length")

    def __contains__(self, word):
        r"""
        Returns ``True`` if ``word`` belongs to ``self``, ``False`` otherwise.

        INPUT:

        - ``word`` -- the word to test

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
        """
        g = self.generator_polynomial()
        R = self._polynomial_ring
        return (g.right_divides(R(word.list())) and word in self.ambient_space())

    def _repr_(self):
        r"""
        Returns a string representation of ``self``.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
        """
        return ("[%s, %s] Skew Cyclic Code over %s"
                % (self.length(), self.dimension(),
                   self.base_field()))

    def generator_polynomial(self):
        r"""
        Returns the generator polynomial of ``self``.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
        """
        return self._generator_polynomial
