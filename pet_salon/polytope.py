def is_subpolytope(polytope, potential_subpolytope):
    r'''Return `True` if `potential_subpolytope` is contained in `polytope`.
    Return `False` otherwise.

    This function checks to see if all the vertices of `potential_subpolytope`
    are contained in `polytope`. It is not clear if this is the best algorithm.
    '''
    # TODO: Check if there is a better algorithm.
    for v in potential_subpolytope.vertices():
        if not polytope.contains(v):
            return False
    return True
