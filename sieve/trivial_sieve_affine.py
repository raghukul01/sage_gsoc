r"""
some things are assuemd to be correct
    1) hash function exists for affine_point
    2) .rational_points yeild correct result
"""

def sieve_tivial(S, bound):
    r"""
    computes rational point less than bound for an affine scheme,
    but using the rational_point function of projective scheme
    """
    pi = S.projective_embedding(0)
    P = pi.codomain()

    AA = P.affine_patch(0)
    
    proj_L = P.rational_points(bound)
    LL = set()
    for point in proj_L:
        pt = []
        denom = point[0]
        if denom == 0:
            continue

        for i in range(1,len(point)):
            pt.append(point[i] / denom)
        LL.add(AA(pt))

    return sorted(list(LL))