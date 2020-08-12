# Auxiliary functions
def computeOrder(sigma, aut_group_order):
    '''
    Computes the order of an autormophism
    Parameters:
        * sigma: automorphism
        * aut_group_order: order of the autormophisms group
    Returns:
        Order of sigma
    '''
    for i in range(1, aut_group_order + 1):
        if (sigma**i).is_identity():
            return i

def RightExtendedEuclideanAlgorithm(f, g):
    '''
    Implementation of the right extended euclidean algorithm
    Parameters:
        * f: first skew polynomial
        * g: second skew polynomial
    Returns:
        Arrays u, v, and r such that f*u[i] + g*v[i] = r[i] for all i
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
    return (u, v, r)
