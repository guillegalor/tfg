load("skew_cyclic_code.sage")

F.<t> = GF(3^10)
sigma = F.frobenius_endomorphism()
n = sigma.order()

R.<x> = F['x', sigma]

# Sample polynomials
a = t + x + 1;
b = R([t^2,t+1,1])

f = a*b
g = x**5 - 1

C = SkewCyclicCode(generator_pol=g)
E = SkewCyclicCodeVectorEncoder(C)
E1 = SkewCyclicCodePolynomialEncoder(C)

alpha = t

RS_C = SkewRSCyclicCode(r=0, hamming_dist=7, skew_polynomial_ring=R, alpha=alpha)
D = SkewRSCyclicCodeSugiyamaDecoder(RS_C)

codeword = RS_C.encode(vector(F, [t,1,t**2,1]))
codeword == D.decode_to_code(codeword)

noisy_codeword = copy(codeword)
noisy_codeword[3] = 1
decoded_word = D.decode_to_code(noisy_codeword)
codeword == decoded_word
