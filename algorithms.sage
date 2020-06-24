# Auxiliary functions
def computeOrder(sigma, aut_group_order):
    '''
    Computes the order of an autormophism
    Parameters:
        * sigma: Automorphism
        * aut_group_order: Order of the autormophisms group
    '''
    for i in range(1, aut_group_order):
        if (sigma**i).is_identity():
            return i

def ExtendedEuclideanAlgorithm(f, g, ):
    # Initialization
    output = []
    output.append((f,1,0))
    output.append((g,0,1))

    q = 0
    rem = 0

    current_uvr =
    while r
