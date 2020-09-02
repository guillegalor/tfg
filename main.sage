load("skew_cyclic_code.sage")

#####################
# Skew Cyclic Codes #
#####################

F.<t> = GF(3^10)
sigma = F.frobenius_endomorphism()
R.<x> = F['x', sigma]

# Sample polynomials
a = t + x + 1;
b = R([t^2,t+1,1])
f = a*b
g = x**5 - 1

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
beta = sigma(t)* t**(-1)
b_roots = [(sigma**i)(beta) for i in range(6)]
pols = [x - b_root for b_root in b_roots]

RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)

P_E = SkewCyclicCodePolynomialEncoder(RS_C)
D = SkewRSCodeSugiyamaDecoder(RS_C)
m = x + t

codeword = P_E.encode(m)
codeword == D.decode_to_code(codeword)

noisy_codeword = copy(codeword)
noisy_codeword[3] = t**671

decoded_word = D.decode_to_code(noisy_codeword)
codeword == decoded_word

# Example Skew RS Convolutional Codes
K.<a> = GF(2^3, 'a', modulus=x**3 + x + 1)
F.<t> = FunctionField(K)
sigma = F.hom((t +a)/t)
R.<x> = F['x', sigma]

alpha = t
RS_C = SkewRSCode(hamming_dist=5, skew_polynomial_ring=R, alpha=alpha)
P_E = SkewCyclicCodePolynomialEncoder(RS_C)
D = SkewRSCodeSugiyamaDecoder(RS_C)

codeword = P_E.encode(R(1))
noisy_codeword = copy(codeword)
noisy_codeword[1] = 0
noisy_codeword[2] = 0

# decoded_word = D.decode_to_code(noisy_codeword)
# codeword == decoded_word
