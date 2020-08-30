import math
import numpy as np

from sage.coding.linear_code import (AbstractLinearCode)
from sage.coding.cyclic_code import _to_complete_list
from sage.coding.encoder import Encoder
from sage.coding.decoder import Decoder
from sage.matrix.constructor import matrix

def right_extended_euclidean_algorithm(skew_polynomial_ring, f, g):
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
    return (i, (u, v, r))

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

def norm(sigma, j, gamma):
    '''
    Computes the ``j``-th norm of ``gamma``.

    INPUT:

    - ``sigma`` -- field automorphism of the field where ``gamma`` is defined
    - ``j`` -- an integer
    - ``gamma`` -- a field element

    OUTPUT
    -- ``a`` -- an element from the same field as gamma
    '''
    if j > 0:
        return np.prod([(sigma**k)(gamma) for k in range(j)])
    elif j < 0:
        return np.prod([(sigma**-k)(gamma) for k in range(-j)])
    else:
        raise ValueError("The second argument must be non zero")

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
        sage: g = x**5 - 1
        sage: C = SkewCyclicCode(generator_pol=g)
        sage: C
        [10, 5] Skew Cyclic Code over Finite Field in t of size 3^10
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

            # TODO Add proper enconder and decoder
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
            sage: g = x**5 - 1
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
            sage: g = x**5 - 1
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: C
            [10, 5] Skew Cyclic Code over Finite Field in t of size 3^10
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
            sage: g = x**5 - 1
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: C.generator_polynomial()
            x^5 + 2
        """
        return self._generator_polynomial

class SkewRSCyclicCode(SkewCyclicCode):
    r"""
    Representation of a skew RS cyclic code.

    A skew RS cyclic code can be constructed by providing,

    - a normal generator of the field extension of the fixed field of sigma into
    the skew polynomial ring base field

    INPUT:

    - ``r`` -- (default: ``None``) the initial exponent to compute the first b-root.
    - ``hamming_dist`` -- (default: ``None``) the desired hamming distance of the code.
    - ``skew_polynomial_ring`` -- (default: ``None``) the base skew polynomial ring.
    - ``alpha`` -- (default: ``None``) a normal generator of the field extension given by sigma.

    EXAMPLES:

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        sage: RS_C = SkewRSCyclicCode(r=0, hamming_dist=4, skew_polynomial_ring=R, alpha=t)
        sage: RS_C
        [10, 7] Skew Reed Solomon Cyclic Code over Finite Field in t of size 3^10
    """
    def __init__(self, r=None, hamming_dist=None, skew_polynomial_ring=None, alpha=None):
        r"""
        TESTS:

        We check that, if `beta = alpha^(-1)*sigma(alpha)`, the left least common multiple of
        the set `[x - beta, x - sigma(beta), ..., x - sigma^(n-1)(beta)]` is `x^n - 1` where
        `n` is the length of the code::

        EXAMPLES:

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: RS_C = SkewRSCyclicCode(r=0, hamming_dist=4, skew_polynomial_ring=R, alpha=t)

            TODO
        """

        if (r is not None and hamming_dist is not None
                and alpha is not None and skew_polynomial_ring is not None):
            F = skew_polynomial_ring.base_ring()
            R = skew_polynomial_ring
            sigma = R.twist_map()
            length = sigma.order()
            beta = alpha**(-1) * sigma(alpha)
            delta = hamming_dist
            x = R.gen()

            factors = [R(x - (sigma**k)(beta)) for k in range(length)]

            if left_lcm(factors) is not R(x**length - 1):
                    raise ValueError("Provided alpha must be an element of the underlying field F of"
                            "the skew polynomial ring provided such that the set "
                            "{alpha, sigma(alpha), ..., sigma^{n-1}(alpha)} is a base "
                            "of F seen as a F^sigma vector space")

            generator_pol = left_lcm(factors[r:r+delta-1])
            deg = generator_pol.degree()

            self._skew_polynomial_ring = R
            self._dimension = length - deg
            self._ring_automorphism = sigma
            self._generator_polynomial = generator_pol
            self._hamming_dist = len(factors) + 1
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

        return ("[%s, %s] Skew Reed Solomon Cyclic Code over %s"
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
        sage: g = x**5 - 1
        sage: C = SkewCyclicCode(generator_pol=g)
        sage: E = SkewCyclicCodeVectorEncoder(C)
        sage: E.encode(vector(F, [0,1,1,2,t]))
        (0, 2, 2, 1, 2*t, 0, 1, 1, 2, t)
    """

    def __init__(self, code):
        r"""

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**5 - 1
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
            sage: g = x**5 - 1
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
            sage: g = x**5 - 1
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodeVectorEncoder(C)
            sage: E
            Vector-style encoder for [10, 5] Skew Cyclic Code over Finite Field in t of size 3^10
        """
        return "Vector-style encoder for %s" % self.code()

    def generator_matrix(self):
        r"""
        Returns a generator matrix of ``self``

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: g = x**5 - 1
            sage: C = SkewCyclicCode(generator_pol=g)
            sage: E = SkewCyclicCodeVectorEncoder(C)
            sage: E.generator_matrix()
            [2 0 0 0 0 1 0 0 0 0]
            [0 2 0 0 0 0 1 0 0 0]
            [0 0 2 0 0 0 0 1 0 0]
            [0 0 0 2 0 0 0 0 1 0]
            [0 0 0 0 2 0 0 0 0 1]
        """
        C = self.code()
        k = C.dimension()
        n = C.length()
        sigma = C._ring_automorphism
        l = _to_complete_list(C.generator_polynomial(), n)
        M = matrix([list(map(sigma**i, l[-i:])) + list(map(sigma**i,l[:-i])) for i in range(k)])
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

        sage: F.<t> = GF(3^10)
        sage: sigma = F.frobenius_endomorphism()
        sage: R.<x> = F['x', sigma]
        sage: RS_C = SkewRSCyclicCode(r=0, hamming_dist=4, skew_polynomial_ring=R, alpha=t)
        sage: D = SkewRSCyclicCodeSugiyamaDecoder(RS_C)
        sage: D
        Decoder through the Sugiyama like algorithmc of the [10, 7] Skew Reed Solomon Cyclic
        Code over Finite Field in t of size 3^10
    """
    def __init__(self, code, **kwargs):
        r"""
        Constructor for this decoder
        """
        super(SkewRSCyclicCodeSugiyamaDecoder, self).__init__(
            code, code.ambient_space(), "SkewCyclicCodeVectorEncoder")

    def __eq__(self, other):
        r"""
        Tests equality between SkewRSCyclicCodeSugiyamaDecoder objects.

        EXAMPLES::

            sage: F.<t> = GF(3^10)
            sage: sigma = F.frobenius_endomorphism()
            sage: R.<x> = F['x', sigma]
            sage: RS_C = SkewRSCyclicCode(r=0, hamming_dist=4, skew_polynomial_ring=R, alpha=t)
            sage: D1 = SkewRSCyclicCodeSugiyamaDecoder(RS_C)
            sage: D2 = SkewRSCyclicCodeSugiyamaDecoder(RS_C)
            sage: D1 == D2
            True
        """
        return (isinstance(other, SkewRSCyclicCodeSugiyamaDecoder) and
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
        Decodes ``y`` to an element in :meth:`sage.coding.encoder.Encoder.code`.

        EXAMPLES::

            TODO
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

        # Step 1: compute the syndrome polynomial
        S = R(0)
        for i in range(2*tau):
            S_i = sum([R(y[j]*norm(sigma, j, (sigma**i)(beta))) for j in range(n)])
            S = S + (sigma**i)(alpha) * S_i * x**i

        # If the syndrome polynomial is zero, the received word is in the code
        if S.is_zero():
            return vector(_to_complete_list(y, n))

        # Step 2: compute the coefficients from right extended euclidean algorithm
        # and find the first index such that deg(r_i) < tau
        l, (u,v,r) = right_extended_euclidean_algorithm(R, R(x**(2*tau)), S)

        I = 0
        for (i, r_i) in enumerate(r):
            if r_i.degree() < tau:
                I = i
                break
        if not I:
            raise RuntimeError("Unexpected error while computing I")

        # Step 3: create the set of error positions and obtain the error locator(lambda)
        # and error evaluator(omega) polynomials.
        pos = []
        for i in range(n):
            if (R(x - (sigma**(i-1))(beta**(-1)))).left_divides(v[I]):
                pos.append(i)

        error_locator_pol = v[I]
        error_evaluator_pol = r[I]

        # If a key equation error occurs (deg(v_i) > Cardinal(pos)), compute the set
        # of error positions and these polynomials using the failure solver algorithm
        if v[I].degree() > len(pos):
            error_locator_pol, error_evaluator_pol, pos = _failure_solver(v[I], r[I], pos)

        # Step 4: compute polynomials p_j such that lambda = (1 - sigma^(k_j)(beta)x)p_j
        p = {}
        for j in pos:
            p[j] = (error_locator_pol.left_quo_rem(R(1 - (sigma**j)(beta)*x)))[0]

        # Step 5: solve the linear system: omega = \sum_{j \in pos} e_j sigma^j(alpha) p_j
        omega = _to_complete_list(error_evaluator_pol, tau)
        Sigma = matrix([[(sigma**j)(alpha) * p[j][i] for j in pos] for i in range(tau)])
        E = Sigma.transpose().solve_left(vector(omega))

        # Step 6: compute the error, and substract if from the received word, obtaining the
        # decoded codeword
        e = sum([E[j] * x**(pos[j]) for j in range(len(pos))])

        return vector(_to_complete_list(y - e, n))

    def _find_a_position(self, p, pos)
        r"""
        Return a new error position that is not in `pos`.

        INPUT:

        - ``p`` -- non constant polynomial from ``self.skew_polynomial_ring``such that
        the error locator polynomial equals p*g for some g in ``self._skew_polynomial_ring``
        - ``pos`` -- a list of integers such that (1 - sigma^d (beta)x)
        left divides p

        OUTPUT:

        - ``i`` -- an integer representing the new error position

        """
        C = self.code()

        R = C._skew_polynomial_ring
        n = C.length()
        sigma = C._ring_automorphism
        beta = C._beta
        x = R.gen()

        f = p
        epsilon = f.degree()

        for i in range(n):
            if i not in pos:
                f = f._right_lcm(R(1 - (sigma**i)(beta) * x))
                if f.degree() = epsilon:
                    return i
                else:
                    epsilon = epsilon + 1

        raise RuntimeError("Unexpected error while computing a new error position")

    def _failure_solver(self, vI, rI, pos)
        r"""
        Computes the error locator polynomial, the error evaluator polynomial and the
        set of error positions

        INPUT:

        - ``vI`` -- a skew polynomial from ``self._skew_polynomial_ring`` such that the
        error locator pol equals vI*g for some g
        - ``rI`` -- a skew polynomial from ``self._skew_polynomial_ring`` such that the
        error evaluator pol equals rI*g for the same g as for vI
        --``pos`` -- a list of integers containing the positions i such that
        (1 - sigma^i(beta)x) left divides v_I

        OUTPUT:
        - ``lambda`` -- error locator polynomial
        - ``omega`` -- error evaluator polynomial
        - ``err_pos`` -- a list contaning all the error positions
        """
        C = self.code()

        R = C._skew_polynomial_ring
        n = C.length()
        sigma = C._ring_automorphism
        beta = C._beta
        x = R.gen()
        err_pos = copy(pos)

        f = vI

        while len(err_pos) < f.degree():
            d = _find_a_err_position(f, err_pos)
            f = f.right_lcm(R(1 - (sigma**d)(beta) * x))

            for i in range(n):
                if i not in err_pos and f.is_left_divisible_by(R(1 - (sigma**i)(beta) * x)):
                    err_pos.append(i)

        g = f.left_quo_rem(vI)

        return f, rI*g, err_pos

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

####################### registration ###############################
SkewCyclicCode._registered_encoders["Vector"] = SkewCyclicCodeVectorEncoder
SkewCyclicCode._registered_decoders["Syndrome"] = LinearCodeSyndromeDecoder

SkewRSCyclicCode._registered_decoders["Sugiyama"] = SkewRSCyclicCodeSugiyamaDecoder
