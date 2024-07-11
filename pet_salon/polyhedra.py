r"""
Examples of polyhedra. 

See also [polytopes from sage.geometry.polyhedron.library](https://doc.sagemath.org/html/en/reference/discrete_geometry/sage/geometry/polyhedron/library.html).
"""

from copy import copy
from sage.geometry.polyhedron.constructor import Polyhedron
from sage.geometry.polyhedron.parent import Polyhedra
from sage.modules.free_module_element import vector

def rectangle(field, *args):
    r'''
    Create a rectangular box from a field and a list of minimal and maximal coordinate values.
    
    For example:
    ```
    rectangle(QQ, 0, 1, 2, 3, 4, 5)
    ```
    constructs the box `[0,1]x[2,3]x[4,5]` over `QQ`.
    
    An even number of coordinates must be provided, and the number of coordinates divided by two
    will be the dimension of the box. The optional field parameter defines the field containing
    the vertices of the box.
    
    EXAMPLES::
    
        sage: from pet_salon.polyhedra import rectangle
        sage: rectangle(QQ, 0, 1, 2, 3, 4, 5)
        A 3-dimensional polyhedron in QQ^3 defined as the convex hull of 8 vertices
    '''
    assert len(args)%2 == 0, 'We require an even number of non-keyword parameters'
    dim = int(len(args)/2)
    P = Polyhedra(field, dim)
    for i in range(dim):
        assert args[2*i] != args[2*i+1], f'A min/max pair matches in index {2*i} and {2*i+1}'
    v = vector(field, [args[i] for i in range(0, 2*dim, 2)])
    vertices = []
    finished = False
    while not finished:
        for i in range(0, dim+1):
            if i==dim:
                finished = True
                break
            if v[i] == args[2*i+1]:
                v[i] = args[2*i]
            else:
                v[i] = args[2*i+1]
                #print(f'i ={i}, v = {v}')
                break
        vertices.append(copy(v))
        #print(vertices)
    return P(Polyhedron(vertices=vertices))
