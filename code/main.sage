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

load("skew_cyclic_code.sage")

###################################
# Examples of auxiliary functions #
###################################

F.<t> = GF(3^10)
sigma = F.frobenius_endomorphism()
R.<x> = F['x', sigma]

a = x + t +1;
b = t^2 * x**2 + (t+1)*x +1
f = a*b
g = b
h = a

left_extended_euclidean_algorithm(R, f, g)
right_extended_euclidean_algorithm(R, f, h)
left_lcm((a,b))
norm(2, sigma, t**2 + t)

#####################
# Skew Cyclic Codes #
#####################

F.<t> = GF(3^10)
sigma = F.frobenius_endomorphism()
R.<x> = F['x', sigma]

# Sample polynomials
g = x**2 + t**24561*x + t**47264

C = SkewCyclicCode(generator_pol=g)
V_E = SkewCyclicCodeVectorEncoder(C)
P_E = SkewCyclicCodePolynomialEncoder(C)

#################
# Skew RS Codes #
#################

# Example Skew RS Block Codes
F.<t> = GF(2^12, modulus=x**12 + x**7 + x**6 + x**5 + x**3 + x +1)
sigma = (F.frobenius_endomorphism())**10
R.<x> = F['x', sigma]

alpha = t

RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)

P_E = SkewCyclicCodePolynomialEncoder(RS_C)
D = SkewRSCodeSugiyamaDecoder(RS_C)
m = x + t

codeword = P_E.encode(m)
codeword == D.decode_to_code(codeword)

noisy_codeword = copy(codeword)
noisy_codeword[3] = t**671

decoded_word = D.decode_to_code(noisy_codeword)
codeword == decoded_wordk
