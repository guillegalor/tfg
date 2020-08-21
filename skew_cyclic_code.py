import math
import numpy as np

from sage.coding.linear_code import (AbstractLinearCode)
from sage.coding.cyclic_code import _to_complete_list
from sage.coding.encoder import Encoder
from sage.coding.decoder import Decoder
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

def left_lcm(pols):
    '''
    TODO Doc
    '''
    llcm = pols[0]
    for p in pols[1:]:
        llcm = llcm.left_lcm(p)

    return llcm

def norm(sigma, j, gamma):
    '''
    TODO
    '''
    if j > 0:
        return np.prod([(sigma**k)(gamma) for k in range(j)])
    elif j < 0:
        return np.prod([(sigma**-k)(gamma) for k in range(-j)])
    else:
        raise ValueError("The second argument must be non zero")

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

        And we check that the generator polynomial right divides `x^{n} - 1`,
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
        if (generator_pol is not None):
            F = generator_pol.base_ring()
            R = generator_pol.parent()
            length = R.twist_map()
            deg = generator_pol.degree()
            if not generator_pol.right_divides(R.gen() ** length - 1):
                raise ValueError("Provided polynomial must divide x^n - 1, "
                                 "where n is the order of the ring automorphism.")
            self._skew_polynomial_ring = R
            self._dimension = length - deg
            self._ring_automorphism = R.twist_map()
            if not generator_pol.is_monic():
                self._generator_polynomial = generator_pol.right_monic()
            else:
                self._generator_polynomial = generator_pol

            # TODO Add proper enconder and decoder
            super(SkewCyclicCode, self).__init__(F, length, "SkewCyclicCodeVectorEncoder", "Syndrome")

        else:
            raise AttributeError("You must provide a generator polynomial")

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
            sage: R.<x> = F['x', sigma] ...
            TODO
            ...
        """
        return self._generator_polynomial

class SkewRSCyclicCode(SkewCyclicCode):
    _registered_encoders = {}
    _registered_decoders = {}

    def __init__(self, generator_pol=None, hamming_dist=None ,b_roots=None):
        r"""
        TESTS:

        If a generator polynomial is provided, the same checkings as in
        SkewCyclicCode are made

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
            Traceback (most recent call last):
            ...
            ValueError:

        Otherwise, we check that each of the polynomials `x - b_roots[i]`
        right divides `x^n - 1`

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
        if (generator_pol is not None and hamming_dist is not None
                and b_roots is None):
            if hamming_dist is not generator_pol.degree() + 1:
                raise ValueError("The Hamming distance of a SkewRSCyclicCode coincides"
                    "with the degree of its generator polynomial plus one")

            _hamming_dist = hamming_dist
            super(SkewCyclicCode, self).__init__(generator_pol)

        elif (b_roots is not None and generator_pol is None
                and hamming_dist is None):
            if not b_roots:
                raise ValueError("Provided b-roots list must not be empty")

            F = b_roots[0].base_ring()
            R = b_roots[0].parent()
            length = R.twist_map()

            factors = [R(R.gen() - b_root) for b_root in b_roots]
            for f in factors:
                if not f.right_divides(R(R.gen() ** length - 1)):
                    raise ValueError("Provided b-roots must divide x^n - 1, "
                                 "where n is the order of the ring automorphism.")

            generator_pol = left_lcm(factors)
            deg = generator_pol.degree()

            self._skew_polynomial_ring = R
            self._dimension = length - deg
            self._ring_automorphism = R.twist_map()
            self._generator_polynomial = generator_pol
            self._hamming_dist = len(b_roots) + 1

            # TODO Add proper enconder and decoder
            super(SkewRSCyclicCode, self).__init__(F, length, "SkewCyclicCodeVectorEncoder", "Syndrome")

        else:
            raise AttributeError("You must provide either a generator polynomial,"
                                 "or a list of b-roots")

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
        return ("[%s, %s] Skew Reed Solomon Cyclic Code over %s"
                % (self.length(), self.dimension(),
                   self.base_field()))

    def hamming_dist(self):
        r"""
        TODO
        """
        return self._hamming_dist

class SkewCyclicCodeVectorEncoder(Encoder):
    r"""
    An encoder which can encode vectors into codewords.

    Let `C` be a skew cyclic code over some skew polynomial ring
    `F[x, \sigma]`, and let `g` be its generator polynomial.

    Let `m = (m_1, m_2, \dots, m_k)` be a vector in `F^{k}`.
    This codeword can be seen as a polynomial over `F[x]`, as follows:
    `P_m = \Sigma_{i=0}^{k-1} m_i \times x^i`.

    To encode `m`, this encoder does the following multiplication:
    `P_m \times g`.

    INPUT:

    - ``code`` -- The associated code of this encoder

    EXAMPLES::

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        ...
        TODO
        ...
    """

    def __init__(self, code):
        r"""

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
        """
        if not isinstance(code, SkewCyclicCode):
            raise ValueError("code has to be a CyclicCode")
        self._polynomial_ring = code._polynomial_ring
        super(SkewCyclicCodeVectorEncoder, self).__init__(code)

    def __eq__(self, other):
        r"""
        Tests equality between SkewCyclicCodeVectorEncoder objects.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
        """
        return (isinstance(other, SkewCyclicCodeVectorEncoder) and
                self.code() == other.code())

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
        return "Vector-style encoder for %s" % self.code()

    def generator_matrix(self):
        r"""
        Returns a generator matrix of ``self``

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            ...
            TODO
            ...
        """
        C = self.code()
        k = C.dimension()
        n = C.length()
        sigma = C._automorphism
        l = _to_complete_list(C.generator_polynomial(), n)
        M = matrix([(sigma**i)(l[-i:]) + (sigma**i)(l[:-i]) for i in range(k)])
        M.set_immutable()
        return M

class SkewRSCyclicCodeSugiyamaDecoder(Decoder):
    r"""
    A decoder which decodes through a algorithm similar to the classic Sugiyama
    algorithm for BCH codes.

    INPUT:

    - ``code`` -- The associated code of this decoder.

    - ``**kwargs`` -- All extra arguments are forwarded to the BCH decoder

    EXAMPLES::

        sage: C = codes.SkewRSCyclicCode(...)
        sage: D = codes.decoders.SkewRSCyclicCodeSugiyamaDecoder(C)
        sage: D
        Decoder through the Sugiyama like algorithmc of the [15, 10] ...
    """
    def __init__(self, code, **kwargs):
        r"""

        EXAMPLES::

            sage: C = codes.SkewRSCyclicCode(field=GF(16), length=15, D=[14, 1, 2, 11, 12])
            sage: D = codes.decoders.CyclicCodeSurroundingBCHDecoder(C)
            sage: D
            Decoder through the surrounding BCH code of the [15, 10] Cyclic Code over GF(16)
        """
        super(SkewRSCyclicCodeSugiyamaDecoder, self).__init__(
            code, code.ambient_space(), "SkewCyclicCodeVectorEncoder")

    def __eq__(self, other):
        r"""
        Tests equality between SkewRSCyclicCodeSugiyamaDecoder objects.

        EXAMPLES::

            sage: C = codes.CyclicCode(field=GF(16), length=15, D=[14, 1, 2, 11, 12])
            sage: D1 = C.decoder()
            sage: D2 = C.decoder()
            sage: D1 == D2
            True
        """
        return (isinstance(other, SkewRSCyclicCodeSugiyamaDecoder) and
                self.code() == other.code())

    def _repr_(self):
        r"""
        Returns a string representation of ``self``.

        EXAMPLES::

            sage: C = codes.CyclicCode(field=GF(16), length=15, D=[14, 1, 2, 11, 12])
            sage: D = codes.decoders.CyclicCodeSurroundingBCHDecoder(C)
            sage: D
            Decoder through the surrounding BCH code of the [15, 10] Cyclic Code over GF(16)
        """
        return ("Decoder through the Sugiyama like algorithmc of the %s" %
                self.code())

    def _latex_(self):
        r"""
        Returns a latex representation of ``self``.

        EXAMPLES::

            sage: C = codes.CyclicCode(field=GF(16), length=15, D=[14, 1, 2, 11, 12])
            sage: D = codes.decoders.CyclicCodeSurroundingBCHDecoder(C)
            sage: latex(D)
            \textnormal{Decoder through the surrounding BCH code of the }[15, 10] \textnormal{ Cyclic Code over } \Bold{F}_{2^{4}}
        """
        return ("\\textnormal{Decoder through the Sugiyama like algorithmc of "
                "the }%s" % self.code()._latex_())

    def decode_to_code(self, y):
        r"""
        Decodes ``r`` to an element in :meth:`sage.coding.encoder.Encoder.code`.

        EXAMPLES::

            sage: F = GF(16, 'a')
            sage: C = codes.CyclicCode(field=F, length=15, D=[14, 1, 2, 11, 12])
            sage: a = F.gen()
            sage: D = codes.decoders.CyclicCodeSurroundingBCHDecoder(C)
            sage: y = vector(F, [0, a^3, a^3 + a^2 + a, 1, a^2 + 1, a^3 + a^2 + 1, a^3 + a^2 + a, a^3 + a^2 + a, a^2 + a, a^2 + 1, a^2 + a + 1, a^3 + 1, a^2, a^3 + a, a^3 + a])
            sage: D.decode_to_code(y) in C
            True
        """

        C = self.code()
        k = C.dimension()
        n = C.length()
        R = C._skew_polynomial_ring
        sigma = R.twist_map()
        generator_pol = C.generator_polynomial()
        tau = self.decoding_radius()

        S = 0
        for i in range(2*tau - 1):
            S_i = sum([R(y[j]*norm(sigma, j, (sigma**i)(beta))) for j in range(n)])

        return self.bch_code().decode_to_code(y)

    def decoding_radius(self):
        r"""
        Returns maximal number of errors that ``self`` can decode.

        EXAMPLES::

            sage: C = codes.CyclicCode(field=GF(16), length=15, D=[14, 1, 2, 11, 12])
            sage: D = codes.decoders.CyclicCodeSurroundingBCHDecoder(C)
            sage: D.decoding_radius()
            1
        """
        return (self.code().hamming_dist() - 1) // 2
