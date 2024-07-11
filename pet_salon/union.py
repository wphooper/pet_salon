from sage.geometry.polyhedron.parent import Polyhedra
from sage.rings.infinity import infinity
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.categories import Unions as UnionsCategory
from pet_salon.categories import PointSets as PointSetsCategory

class Union(Element):
    def __init__(self, parent):
        Element.__init__(self, parent)

    def __eq__(self, other):
        if self is other:
            return True
        if not isinstance(other, Union):
            return False
        if self.parent() != other.parent():
            return False
        if self.size() != other.size():
            return False
        if self.size() == infinity:
            return False
        if self.labels() != other.labels():
            return False
        for label in self.labels():
            if self.piece(label) != other.piece(label):
                return False
        return True

    def __hash__(self):
        if self.size() == infinity:
            size = 10
        else:
            size = self.size()
        return hash(tuple([self.parent(),] + \
                          [(label, self.piece(label)) for i,label in zip(range(size), self.labels())]
                         ))

    def __repr__(self):
        s = str(self.parent().polyhedra())
        return f'Disjoint union of {self.size()} {s[0].lower()}{s[1:]}'

class FiniteUnion(Union):
    def __init__(self, parent, label_to_subpolyhedron_dict):
        Union.__init__(self, parent)
        P = self.parent().polyhedra()
        assert isinstance(label_to_subpolyhedron_dict, dict), \
            'A dictionary must be passed to the constructor'
        self._dict = {}
        for label,poly in label_to_subpolyhedron_dict.items():
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
        s = str(self.parent().polyhedra())
        return f'Disjoint union of {self.size()} {s[0].lower()}{s[1:]}'

class FiniteUnions(UniqueRepresentation, Parent):
    r'''
    Parent for domains of PETs of a given dimension that are defined over a given field.
    '''
    Element = FiniteUnion

    def __init__(self, dimension, field):
        Parent.__init__(self, category=UnionsCategory.Finite(field))
        self._n = dimension
        self.rename(f'Finite disjoint unions of polyhedra in dimension {self._n} over {self.base_ring()}')

    def base_ring(self):
        r"""
        Return the ring over which this subdivision is defined.
        """
        return self.category().base_ring()

    
    def __eq__(self, other):
        if not isinstance(other, FiniteUnions):
            return False
        return self.dimension() == other.dimension() and self.base_ring() == other.base_ring()

    def __hash__(self):
        return hash((self.dimension(), self.category().base_ring()))
    
    def dimension(self):
        r'''
        Return the dimension of the domains.
        '''
        return self._n

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
            if isinstance(args[0], Union):
                if not args[0].is_finite():
                    raise ValueError('Conversion to finite union not implemented yet')
                d = {label:args[0].piece(label) for label in args[0].labels()}
                return self.element_class(self, d)
            elif isinstance(args[0], dict):
                return self.element_class(self, args[0])
            else:
                raise ValueError('Conversion not implemented yet')
        raise ValueError('Unclear how creata a finite union from passed parameters')
    
    def _an_element_(self):
        from sage.geometry.polyhedron.library import polytopes
        P = self.polyhedra()
        p0 = P(polytopes.hypercube(self.dimension()))
        p1 = P(polytopes.cross_polytope(self.dimension()))
        return self({0:p0, 1:p1})

class Point(Element):
    def __init__(self, parent, label, vector):
        self._label = label
        self._vector = vector
        Element.__init__(self, parent)

    def label(self):
        return self._label

    def vector(self):
        return self._vector

    def __repr__(self):
        return f'Point({self.label()}, {self.vector()})'

    def __eq__(self, other):
        if other is None:
            return False
        if not hasattr(other, 'parent'):
            return False
        if self.parent() != other.parent():
            return False
        if self.label() != other.label():
            return False
        return self.vector() == other.vector()

class PointSet(Parent):
    r'''
    Represents the set of points in a `Union`.

    EXAMPLES::
        sage: from pet_salon.union import FiniteUnions
        sage: U = FiniteUnions(2, QQ)
        sage: union = U.an_element()
        sage: union
        Disjoint union of 2 polyhedra in QQ^2
        sage: PS = union.point_set()
        sage: PS
        PointSet in disjoint union of 2 polyhedra in QQ^2
        sage: TestSuite(PS).run()
        sage: PS.center(0)
        Point(0, (0, 0))
        sage: pt = PS.center(1)
        sage: pt
        Point(1, (0, 0))
        sage: TestSuite(pt).run()
    '''
    Element = Point

    def __init__(self, union):
        assert union.parent().category().is_subcategory(UnionsCategory(union.base_ring())), \
            'union must be a Union'
        Parent.__init__(self, category=PointSetsCategory(union.base_ring()))
        self._union = union
        union_name = repr(union)
        self.rename(f'PointSet in {union_name[0].lower()}{union_name[1:]}')

    def union(self):
        return self._union

    def base_ring(self):
        return self.category().base_ring()

    def __eq__(self, other):
        if not hasattr(other, 'category'):
            return False
        if not other.category().is_subcategory(self.category()):
            return False
        return self.union() == other.union()

    def __hash__(self):
        return hash((self.category(), self.union()))
