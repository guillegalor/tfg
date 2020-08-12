from sage.rings.polynomial.skew_polynomial_element import ConstantSkewPolynomialSection
load("algorithms.sage")

F.<t> = GF(3^10)
Aut = Hom(F, F)
# sigma = Aut.list()[4]
sigma = F.frobenius_endomorphism()
n = sigma.order()

R.<x> = F['x', sigma]

# Sample polynomials
a = t + x + 1;
b = R([t^2,t+1,1])

f = a*b
g = a
