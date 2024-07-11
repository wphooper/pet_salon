from copy import copy
from sage.geometry.polyhedron.constructor import Polyhedron
from sage.geometry.polyhedron.parent import Polyhedra
from sage.rings.integer_ring import ZZ
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.categories import Subdivisions as SubdivisionsCategory
from pet_salon.union import Union, FiniteUnion, FiniteUnions

class Subdivision(Union):
    def __init__(self, parent, polyhedron, category=None):
        Union.__init__(self, parent)
        #if parent is None:
        #    raise ValueError("The parent must be provided")
        #assert isinstance(parent, Subdivisions), 'parent must be an instance of Subdivisions'
        self._p = parent.polyhedra()(polyhedron)
    
    def polyhedron(self):
        return self._p

    def __eq__(self, other):
        if self is other:
            return True
        if not isinstance(other, Subdivision):
            return False
        if self.parent() != other.parent():
            return False
        if self.polyhedron() != other.polyhedron():
            return False
        return Union.__eq__(self, other)

    def __hash__(self):
        if self.size() == infinity:
            size = 10
        else:
            size = self.size()
        return hash(tuple([self.parent(), self.polyhedron()] + \
                          [(label, self.piece(label)) for i,label in zip(range(limit), self.labels())]
                         ))

class FiniteSubdivision(Subdivision,FiniteUnion):
    def __init__(self, parent, polyhedron, label_to_subpolygon_dict):
        Subdivision.__init__(self, parent, polyhedron)
        P = self.parent().polyhedra()
        assert isinstance(label_to_subpolygon_dict, dict)
        self._dict = {}
        for label,poly in label_to_subpolygon_dict.items():
            self._dict[label] = P(poly)

    def labels(self):
        r'''Return the collection of labels in this domain, or an iterator over the labels.'''
        return self._dict.keys()

    def size(self):
        return len(self.labels())
    
    def piece(self, label):
        r'''Return the polyhedron with the given label.'''
        return self._dict[label]

    def __repr__(self):
        return f'Subdivision of {str(self.polyhedron()).lower()} into {self.size()} subpolyhedra'

class FiniteSubdivisions(FiniteUnions):
    Element = FiniteSubdivision

    def __init__(self, dimension, field):
        r'''
        Parent for domains of PETs of a given dimension that are definedover a given field.
        '''
        Parent.__init__(self, category=SubdivisionsCategory.Finite(field))
        self._n = dimension
        self.rename(f'Finite subdivisions in dimension {self._n} over {self.base_ring()}')

    def base_ring(self):
        r"""
        Return the ring over which this subdivision is defined.
        """
        return self.category().base_ring()

    
    def __eq__(self, other):
        if not isinstance(other, FiniteSubdivisions):
            return False
        return self.dimension() == other.dimension() and self.base_ring() == other.base_ring()

    def __hash__(self):
        return hash((self.dimension(), self.category().base_ring()))
    
    def dimension(self):
        r'''
        Return the dimension of the domains.
        '''
        return self._n

    def affine_group(self):
        r'''
        Return the `AffineGroup` with degree equal to the dimension and over the field.
        '''
        return AffineGroup(self._n, self.base_ring())

    def polyhedra(self):
        return Polyhedra(self.category().base_ring(), self._n)

    def __repr__(self):
        return f'Finite subdivisions of polyhedra of dimension {self.dimension()} over {self.category().base_ring()}'

    def find_limit(self):
        if hasattr(self, '_default_find_limit'):
            return self._default_find_limit
        else:
            return 100

    def set_find_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._default_find_limit = limit

    def volume_check_limit(self):
        if hasattr(self, '_volume_check_limit'):
            return self._volume_check_limit
        else:
            return 100

    def set_volume_check_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._volume_check_limit = limit    

    def containment_check_limit(self):
        if hasattr(self, '_containment_check_limit'):
            return self._containment_check_limit
        else:
            return 100

    def set_containment_check_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._containment_check_limit = limit    

    def intersection_check_limit(self):
        if hasattr(self, '_intersection_check_limit'):
            return self._intersection_check_limit
        else:
            return 20

    def set_intersection_check_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._intersection_check_limit = limit    

    def _element_constructor_(self, *args, **kwds):
        #print(f'Called element_constructor with args={args}')
        if len(args)==1:
            if isinstance(args[0], Subdivision):
                if not args[0].is_finite():
                    raise ValueError('Conversion to finite subdivision not implemented yet')
                P = self.polyhedra()
                p = P(args[0].polyhedron())
                d = {label:P(args[0].piece(label)) for label in args[0].labels()}
                return self.element_class(self, p, d)           
            else:
                raise ValueError('Conversion not implemented yet')
        if len(args)==2 and isinstance(args[1], dict):
            return self.element_class(self, args[0], args[1])
        raise ValueError('Unclear how creata a subdivision from passed parameters')

    def trivial_subdivision(self, polyhedron):
        polyhedron = self.polyhedra()(polyhedron)
        return self(polyhedron, {0: polyhedron})
    
    def _an_element_(self):
        v = copy(self.vector_space().zero())
        vertices = [copy(v)]
        for i in range(self.dimension()):
            v[i] = self.category().base_ring().one()
            vertices.append(copy(v))
            v[i] = self.category().base_ring().zero()
        return self.trivial_subdivision(Polyhedron(vertices=vertices))
