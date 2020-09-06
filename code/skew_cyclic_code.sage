# *****************************************************************************
#             Copyright (C) 2020 Guillermo Galindo Ortuño
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
# *****************************************************************************

import math
import numpy as np

from sage.coding.linear_code import (AbstractLinearCode)

from sage.coding.cyclic_code import _to_complete_list
from sage.coding.encoder import Encoder
from sage.coding.decoder import Decoder

from sage.rings.polynomial.skew_polynomial_element import ConstantSkewPolynomialSection
from sage.coding.linear_code import (AbstractLinearCode, LinearCodeSyndromeDecoder)

def left_extended_euclidean_algorithm(skew_polynomial_ring, f, g):
    '''
    Implementation of the left extended euclidean algorithm.

    INPUT:

    - ``f`` -- one skew polynomial.

    - ``g`` -- another skew polynomial.

    OUTPUT:

    - ``u, v, r`` --  with u, v, r arrays of skew polynomials
    such that u[i]*f + v[i]*g = r[i] for all i

    EXAMPLES:

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        sage: a = x + t +1;
        sage: b = t^2 * x**2 + (t+1)*x +1
        sage: f = a*b
        sage: g = b
        sage: left_extended_euclidean_algorithm(R, f, g)
        ([1, 0, 1],
         [0, 1, 2*x + 2*t + 2],
         [t^6*x^3 + (2*t^3 + t^2 + 1)*x^2 + (t^2 + 2*t + 2)*x + t + 1,
          t^2*x^2 + (t + 1)*x + 1,
          0])
    '''
    R = skew_polynomial_ring
    u = [R(1), R(0)]
    v = [R(0), R(1)]
    r = [f, g]

    i = 1
    while r[i] != 0:
        q, rem = r[i-1].right_quo_rem(r[i])
        u.append(u[i-1] - q*u[i])
        v.append(v[i-1] - q*v[i])
        r.append(rem)

        i = i+1
    return u, v, r

def right_extended_euclidean_algorithm(skew_polynomial_ring, f, g):
    '''
    Implementation of the right extended euclidean algorithm.

    INPUT:

    - ``f`` -- one skew polynomial.

    - ``g`` -- another skew polynomial.

    OUTPUT:

    - ``u, v, r`` --  with u, v, r arrays of skew polynomials
    such that f*u[i] + g*v[i] = r[i] for all i

    EXAMPLES:

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        sage: a = x + t +1;
        sage: b = t^2 * x**2 + (t+1)*x +1
        sage: f = a*b
        sage: g = a
        sage: right_extended_euclidean_algorithm(R, f, g)
        ([1, 0, 1],
         [0, 1, 2*t^2*x^2 + (2*t + 2)*x + 2],
         [t^6*x^3 + (2*t^3 + t^2 + 1)*x^2 + (t^2 + 2*t + 2)*x + t + 1, x + t + 1, 0])
    '''
    # Initialization
    R = skew_polynomial_ring
    u = [R(1), R(0)]
    v = [R(0), R(1)]
    r = [f, g]

    i = 1
    while r[i] != 0:
        q, rem = r[i-1].left_quo_rem(r[i])
        u.append(u[i-1] - u[i]*q)
        v.append(v[i-1] - v[i]*q)
        r.append(rem)

        i = i+1
    return u, v, r

def left_lcm(pols):
    '''
    Computes the left least common multiple for a list of skew polynomials

    INPUT:

    - ``pols`` -- a list of skew polynomials

    OUTPUT:

    - ``llcm`` --  a skew polynomial which is one left least common multiple
    '''
    llcm = pols[0]
    for p in pols[1:]:
        llcm = llcm.left_lcm(p)

    return llcm

def norm(j, sigma, gamma):
    '''
    Computes the ``j``-th norm of ``gamma``.

    INPUT:

    - ``sigma`` -- field automorphism of the field where ``gamma`` is defined

    - ``j`` -- an integer

    - ``gamma`` -- a field element

    OUTPUT

    -- ``a`` -- an element from the same field as gamma
    '''
    if j == 0:
        return 1
    elif j > 0:
        return np.prod([(sigma**k)(gamma) for k in range(j)])
    else:
        return np.prod([(sigma**-k)(gamma) for k in range(-j)])

class KeyEquationError(Exception):
    pass

class SkewCyclicCode(AbstractLinearCode):
    r"""
    Representation of a skew cyclic code.

    A skew cyclic code can be constructed by providing,

    - the generator polynomial(1)

    INPUT:

    - ``generator_pol`` -- (default: ``None``) the generator skew polynomial
      of ``self``. That is, the highest-degree monic polynomial which right
      divides every polynomial representation of a codeword in ``self``.

    EXAMPLES:

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        sage: g = x**2 + t**24561*x + t**47264
        sage: C = SkewCyclicCode(generator_pol=g)
        sage: C
        [10, 8] Skew Cyclic Code over Finite Field in t of size 3^10
    """

    _registered_encoders = {}
    _registered_decoders = {}

    def __init__(self, generator_pol=None):
        r"""
        TESTS:

        We check that the generator polynomial right divides `x^{n} - 1`,
        where `n` is the length of the code::

        EXAMPLES:

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**3 - 1
            sage: C = SkewCyclicCode(generator_pol=g)
            Traceback (most recent call last)
            ...
            ValueError: Provided polynomial must divide x^n - 1, where n is
            the order of the ring automorphism.
        """
        if (generator_pol is not None):
            F = generator_pol.base_ring()
            R = generator_pol.parent()
            length = R.twist_map().order()
            deg = generator_pol.degree()
            if not generator_pol.right_divides(R.gen()**length - 1):
                raise ValueError("Provided polynomial must divide x^n - 1, "
                                 "where n is the order of the ring automorphism.")
            self._skew_polynomial_ring = R
            self._dimension = length - deg
            self._ring_automorphism = R.twist_map()
            if not generator_pol.is_monic():
                self._generator_polynomial = generator_pol.right_monic()
            else:
                self._generator_polynomial = generator_pol

            super(SkewCyclicCode, self).__init__(F, length, "Vector", "Syndrome")

        else:
            raise AttributeError("You must provide a generator polynomial")

    def __eq__(self, other):
        r"""
        Tests equality between SkewCyclicCode objects.

        INPUT:

        - ``other`` -- the code to test

        EXAMPLES::
            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C1 = SkewCyclicCode(generator_pol=g)
            sage: C2 = SkewCyclicCode(generator_pol=g)
            sage: C1 == C2
            True
        """
        if not isinstance(other, SkewCyclicCode):
            return False
        else:
            R = self._skew_polynomial_ring
            return (self.base_field() == other.base_field() and
                    self.generator_polynomial() == R(other.generator_polynomial()))

    def _repr_(self):
        r"""
        Returns a string representation of ``self``.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: C
            [10, 8] Skew Cyclic Code over Finite Field in t of size 3^10
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
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: C.generator_polynomial()
            x^2 + ...  + t^5 + t^2 + 2
        """
        return self._generator_polynomial

    def skew_polynomial_ring(self):
        r"""
        Returns the underlying skew polynomial ring of ``self``.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: C.skew_polynomial_ring()
            Skew Polynomial Ring in x over Finite Field in t of
            size 3^10 twisted by t |--> t^3
        """

        return self._skew_polynomial_ring

class SkewRSCode(SkewCyclicCode):
    r"""
    Representation of a skew RS code.

    A skew RS code can be constructed by providing,

    - a normal generator of the field extension of the fixed field of sigma into
    the skew polynomial ring base field

    INPUT:

    - ``hamming_dist`` -- (default: ``None``) the desired hamming distance of the code.

    - ``skew_polynomial_ring`` -- (default: ``None``) the base skew polynomial ring.

    - ``alpha`` -- (default: ``None``) a normal generator of the field extension given by sigma.

    EXAMPLES:

        sage: F.<t> = GF(2^12, modulus=x**12 + x**7 + x**6 + x**5 + x**3 + x +1)
        sage: sigma = (F.frobenius_endomorphism())**10
        sage: R.<x> = F['x', sigma]
        sage: alpha = t
        sage: RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)
        sage: RS_C
        [6, 2] Skew Reed Solomon Code over Finite Field in t of size 2^12
    """

    def __init__(self, hamming_dist=None, skew_polynomial_ring=None, alpha=None):
        r"""
        TESTS:

        We check that, if `beta = alpha^(-1)*sigma(alpha)`, the left least common multiple of
        the set `[x - beta, x - sigma(beta), ..., x - sigma^(n-1)(beta)]` is `x^n - 1` where
        `n` is the length of the code::

        EXAMPLES:

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: RS_C = SkewRSCode(hamming_dist=4, skew_polynomial_ring=R, alpha=t)
            ValueError: Provided alpha must be an normal generator of the field extension given by
            sigma
        """

        if (hamming_dist is not None and alpha is not None
                and skew_polynomial_ring is not None):
            F = skew_polynomial_ring.base_ring()
            R = skew_polynomial_ring
            sigma = R.twist_map()

            length = 0
            try:
                length = sigma.order()
            except AttributeError:
                i = 1
                while length == 0:
                    if (sigma**i).is_one():
                        length = i
                    else:
                        i = i+1

            beta = alpha**(-1) * sigma(alpha)
            delta = hamming_dist
            x = R.gen()

            factors = [R(x - (sigma**k)(beta)) for k in range(length)]

            basis = [(sigma**i)(alpha) for i in range(length)]
            M = matrix([basis[i:] + basis[:i] for i in range(length)])
            if M.det() == 0:
                raise ValueError("Provided alpha must be an normal generator of "
                    "the field extension given by sigma")

            generator_pol = left_lcm(factors[:delta-1])
            deg = generator_pol.degree()

            self._skew_polynomial_ring = R
            self._dimension = length - deg
            self._ring_automorphism = sigma
            self._generator_polynomial = generator_pol
            self._hamming_dist = delta
            self._alpha = alpha
            self._beta = beta

            super(SkewCyclicCode, self).__init__(F, length, "Vector", "Sugiyama")

        else:
            raise AttributeError("You must provide an initial exponent, the desired"
                    " hamming distance, a skew polynomial ring and an element of the"
                    " underlying field")

    def _repr_(self):
        r"""
        Returns a string representation of ``self``.
        """

        return ("[%s, %s] Skew Reed Solomon Code over %s"
                % (self.length(), self.dimension(),
                   self.base_field()))

    def hamming_dist(self):
        r"""
        Returns the hamming distance of ``self``
        """
        return self._hamming_dist

class SkewCyclicCodeVectorEncoder(Encoder):
    r"""
    An encoder which can encode vectors into codewords.

    Let `C` be a skew cyclic code over some skew polynomial ring
    `F[x, \sigma]`, and let `g` be its generator polynomial.

    Let `m = (m_1, m_2, \dots, m_k)` be a vector in `F^{k}`.
    To encode `m`, this encoder computes the generator matrix of `C`,
    let say `G`, so the codeword will be `mG`

    INPUT:

    - ``code`` -- The associated code of this encoder

    EXAMPLES::

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        sage: g = x**2 + t**24561*x + t**47264
        sage: C = SkewCyclicCode(generator_pol=g)
        sage: E = SkewCyclicCodeVectorEncoder(C)
        sage: E.encode(vector(F, [1,t,1,t**2,1,t,1,1]))
        (2*t^9 + t^8 + 2*t^6 + t^5 + t^2 + 2, ... , 1)
    """

    def __init__(self, code):
        r"""

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodeVectorEncoder(C)
        """
        if not isinstance(code, SkewCyclicCode):
            raise ValueError("code has to be a SkewCyclicCode")
        super(SkewCyclicCodeVectorEncoder, self).__init__(code)

    def __eq__(self, other):
        r"""
        Tests equality between SkewCyclicCodeVectorEncoder objects.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E1 = SkewCyclicCodeVectorEncoder(C)
            sage: E2 = SkewCyclicCodeVectorEncoder(C)
            sage: E1 == E2
            True
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
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodeVectorEncoder(C)
            sage: E
            Vector-style encoder for [10, 8] Skew Cyclic Code over Finite Field in t of size 3^10
        """
        return "Vector-style encoder for %s" % self.code()

    def generator_matrix(self):
        r"""
        Returns a generator matrix of ``self``

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodeVectorEncoder(C)
            sage: E.generator_matrix()
            [2*t^9 + t^8 + 2*t^6 + t^5 + t^2 + 2 ... 0]
            [                   ...                   ]
            [                   ...                   ]
            [                   ...                   ]
            [                   ...                   ]
            [                   ...                   ]
            [                   ...                   ]
            [0                  ...                  1]
        """
        C = self.code()
        k = C.dimension()
        n = C.length()
        sigma = C._ring_automorphism
        l = _to_complete_list(C.generator_polynomial(), n)
        M = matrix([list(map(sigma**i, l[-i:])) + list(map(sigma**i,l[:-i])) for i in range(k)])
        M.set_immutable()
        return M

class SkewCyclicCodePolynomialEncoder(Encoder):
    r"""
    An encoder encoding polynomials into codewords.

    Let `C` be a skew cyclic code over some field `F` with twist
    map `sigma`, and let `g` be its generator polynomial.

    This encoder encodes any polynomial `p \in F[x;sigma]_{<k}` by computing
    `c = p \times g` and returning the vector of its coefficients.

    INPUT:

    - ``code`` -- The associated code of this encoder

    EXAMPLES::

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        sage: g = x**2 + t**24561*x + t**47264
        sage: C = SkewCyclicCode(generator_pol=g)
        sage: E = SkewCyclicCodePolynomialEncoder(C)
        sage: E
        Polynomial-style encoder for [10, 8] Skew Cyclic
        Code over Finite Field in t of size 3^10
    """

    def __init__(self, code):
        r"""
        Basic constructor for this encoder
        """
        if not isinstance(code, SkewCyclicCode):
            raise ValueError("code has to be a SkewCyclicCode")
        self._skew_polynomial_ring = code._skew_polynomial_ring
        super(SkewCyclicCodePolynomialEncoder, self).__init__(code)

    def __eq__(self, other):
        r"""
        Tests equality between SkewCyclicCodePolynomialEncoder objects.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E1 = SkewCyclicCodePolynomialEncoder(C)
            sage: E2 = SkewCyclicCodePolynomialEncoder(C)
            sage: E1 == E2
            True
        """
        return (isinstance(other, SkewCyclicCodePolynomialEncoder) and
                self.code() == other.code())

    def _repr_(self):
        r"""
        Returns a string representation of ``self``.
        """
        return "Polynomial-style encoder for %s" % self.code()

    def _latex_(self):
        r"""
        Returns a latex representation of ``self``.
        """
        return ("\\textnormal{Polynomial-style encoder for }%s" %
                self.code()._latex_())

    def encode(self, p):
        r"""
        Transforms ``p`` into an element of the associated code of ``self``.

        INPUT:

        - ``p`` -- A polynomial from ``self`` message space

        OUTPUT:

        - A codeword in associated code of ``self``

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodePolynomialEncoder(C)
            sage: m = x + t + 1
            sage: E.encode(m)
            (t^8 + 2*t^7 + 2*t^6 + 2*t^4 + t^3 + t^2 + 1, ... , 0)
        """
        C = self.code()
        k = C.dimension()
        n = C.length()
        if p.degree() >= k:
            raise ValueError("Degree of the message must be at most %s" % k - 1)
        res = _to_complete_list(p * C.generator_polynomial(), n)
        return vector(C.base_field(), res)

    def unencode_nocheck(self, c):
        r"""
        Returns the message corresponding to ``c``.
        Does not check if ``c`` belongs to the code.

        INPUT:

        - ``c`` -- A vector with the same length as the code

        OUTPUT:

        - An element of the message space

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodePolynomialEncoder(C)
            sage: m = x + t + 1
            sage: w = E.encode(m)
            sage: E.unencode_nocheck(w)
            x + t + 1
        """
        R = self.message_space()
        g = self.code().generator_polynomial()
        p = R(c.list())
        return p // g

    def message_space(self):
        r"""
        Returns the message space of ``self``

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**2 + t**24561*x + t**47264
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodePolynomialEncoder(C)
            sage: E.message_space()
            Skew Polynomial Ring in x over Finite Field in t
            of size 3^10 twisted by t |--> t^3
        """
        return self._skew_polynomial_ring

class SkewRSCodeSugiyamaDecoder(Decoder):
    r"""
    A decoder for skew RS codes which decodes through a algorithm similar to
    the classic Sugiyama algorithm for BCH codes.

    INPUT:

    - ``code`` -- The associated code of this decoder.

    - ``**kwargs`` -- All extra arguments are forwarded to the decoder

    EXAMPLES::

        sage: F.<t> = GF(2^12, modulus=x**12 + x**7 + x**6 + x**5 + x**3 + x +1)
        sage: sigma = (F.frobenius_endomorphism())**10
        sage: R.<x> = F['x', sigma]
        sage: alpha = t
        sage: RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)
        sage: D = SkewRSCodeSugiyamaDecoder(RS_C)
        sage: D
        Decoder through the Sugiyama like algorithm of the [6, 2] Skew Reed Solomon
        Code over Finite Field in t of size 2^12
    """
    def __init__(self, code, **kwargs):
        r"""
        Basic constructor for this decoder
        """
        super(SkewRSCodeSugiyamaDecoder, self).__init__(
            code, code.ambient_space(), "SkewCyclicCodeVectorEncoder")

    def __eq__(self, other):
        r"""
        Tests equality between SkewRSCodeSugiyamaDecoder objects.

        EXAMPLES::
            sage: F.<t> = GF(2^12, modulus=x**12 + x**7 + x**6 + x**5 + x**3 + x +1)
            sage: sigma = (F.frobenius_endomorphism())**10
            sage: R.<x> = F['x', sigma]
            sage: alpha = t
            sage: RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)
            sage: D1 = SkewRSCodeSugiyamaDecoder(RS_C)
            sage: D2 = SkewRSCodeSugiyamaDecoder(RS_C)
            sage: D1 == D2
            True
        """
        return (isinstance(other, SkewRSCodeSugiyamaDecoder) and
                self.code() == other.code())

    def _repr_(self):
        r"""
        Returns a string representation of ``self``.
        """
        return ("Decoder through the Sugiyama like algorithm of the %s" %
                self.code())

    def _latex_(self):
        r"""
        Returns a latex representation of ``self``.
        """
        return ("\\textnormal{Decoder through the Sugiyama like algorithmc of "
                "the }%s" % self.code()._latex_())

    def decode_to_code(self, word):
        r"""
        Decodes ``word`` to an element in :meth:`sage.coding.encoder.Encoder.code`.

        INPUT:

        - `word` -- Vector of `self.code().length()` elements of the field of this code

        EXAMPLES::

            sage: F.<t> = GF(2^12, modulus=x**12 + x**7 + x**6 + x**5 + x**3 + x +1)
            sage: sigma = (F.frobenius_endomorphism())**10
            sage: R.<x> = F['x', sigma]
            sage: alpha = t
            sage: RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)
            sage: D = SkewRSCodeSugiyamaDecoder(RS_C)
            sage: P_E = SkewCyclicCodePolynomialEncoder(RS_C)
            sage: m = x + t
            sage: codeword = P_E.encode(m)
            sage: noisy_codeword = copy(codeword)
            sage: noisy_codeword[3] = t**671
            sage: decoded_word = D.decode_to_code(noisy_codeword)
            sage: codeword == decoded_word
            True
        """
        C = self.code()

        R = C._skew_polynomial_ring
        y = R(word.list())
        n = C.length()
        k = C._dimension
        sigma = C._ring_automorphism
        g = C.generator_polynomial()
        delta = C._hamming_dist
        alpha = C._alpha
        beta = C._beta
        tau = self.decoding_radius()
        x = R.gen()

        S = R(0)

        for i in range(2*tau):
            S_i = sum([R(y[j]*norm(j, sigma, (sigma**i)(beta))) for j in range(n)])
            S = S + (sigma**i)(alpha) * S_i * x**i

        if S.is_zero():
            return vector(_to_complete_list(y, n))

        u, v, r = right_extended_euclidean_algorithm(R, R(x**(2*tau)), S)

        I = 0
        for (i, r_i) in enumerate(r):
            if r_i.degree() < tau:
                I = i
                break
        if not I:
            raise RuntimeError("Error al calcular I")

        pos = []

        for i in range(n):
            if (R(x - (sigma**(i-1))(beta**(-1)))).left_divides(v[I]):
                pos.append(i)

        if v[I].degree() > len(pos):
            raise KeyEquationError

        p = {}
        for j in pos:
            p[j] = (v[I].left_quo_rem(R(1 - (sigma**j)(beta)*x)))[0]

        omega = _to_complete_list(r[I], tau)
        Sigma = matrix([[(sigma**j)(alpha) * p[j][i] for j in pos] for i in range(tau)])

        E = Sigma.transpose().solve_left(vector(omega))
        e = sum([E[j] * x**(pos[j]) for j in range(len(pos))])

        return vector(_to_complete_list(y - e, n))

    def decoding_radius(self):
        r"""
        Returns maximum number of errors that ``self`` can correct.

        EXAMPLES::

            sage: F.<t> = GF(2^12, modulus=x**12 + x**7 + x**6 + x**5 + x**3 + x +1)
            sage: sigma = (F.frobenius_endomorphism())**10
            sage: R.<x> = F['x', sigma]
            sage: alpha = t
            sage: RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)
            sage: D = SkewRSCodeSugiyamaDecoder(RS_C)
            sage: D.decoding_radius()
            2
        """
        return (self.code().hamming_dist() - 1) // 2

####################### registration ###############################
SkewCyclicCode._registered_encoders["Vector"] = SkewCyclicCodeVectorEncoder
SkewCyclicCode._registered_encoders["Polynomial"] = SkewCyclicCodePolynomialEncoder
SkewCyclicCode._registered_decoders["Syndrome"] = LinearCodeSyndromeDecoder

SkewRSCode._registered_decoders["Sugiyama"] = SkewRSCodeSugiyamaDecoder
