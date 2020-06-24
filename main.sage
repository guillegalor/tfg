from sage.rings.polynomial.skew_polynomial_element import ConstantSkewPolynomialSection

F = GF(3^10)
Aut = Hom(F, F)
sigma = Aut.list()[4]
n = computeOrder(sigma, Aut.order())

R.<x> = F['x', sigma]
