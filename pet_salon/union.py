from collections.abc import Mapping
from copy import copy

from sage.categories.all import Sets
from sage.categories.category import Category
from sage.categories.category_with_axiom import CategoryWithAxiom, all_axioms
from sage.geometry.polyhedron.parent import Polyhedra
from sage.misc.cachefunc import cached_method
from sage.misc.abstract_method import abstract_method
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import infinity
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation



# Make DisjointImages an axiom in Sage:
all_axioms += ("DisjointImages",)


class PolytopeUnionsCategory(Category):
    r"""
    The category of indexed disjoint unions of polyhedra.

    EXAMPLES::

        sage: from pet_salon.union import PolytopeUnionsCategory
        sage: PolytopeUnionsCategory()
        Category of disjoint polytope unions
    """

    # TODO: Fix category names. Currently
    # PolytopeUnionsCategory().DisjointImages().Finite()
    # has a nonsensical name.

    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self._fix_name()


    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.union import PolytopeUnionsCategory
            sage: C = PolytopeUnionsCategory()
            sage: C.super_categories()
            [Category of sets]

        """
        return [Sets()]

    class SubcategoryMethods:

        def DisjointImages(self):
            r'''We say a PolytopeUnion has Disjoint images if the polytopes, viewed as subsets of the vector space containing them, have disjoint interiors.

            This will make available the `find` method.'''
            return self._with_axiom('DisjointImages')

        def _fix_name(self):
            if 'DisjointImages' in self.axioms():
                di = ' with disjoint images'
            else:
                di = ''
            if 'Finite' in self.axioms():
                f = 'finite '
            else:
                f = ''
            self.rename(f'Category of {f}disjoint polytope unions{di}')

    class ParentMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """

        @abstract_method
        def field(self):
            pass

        @abstract_method
        def dimension(self):
            pass

        def is_finite(self):
            r'''Return `True` if this parent only contains finite objects.

            Return `False` otherwise.
            '''
            return False

        def has_disjoint_images(self):
            r'''Return `True` if this parent only contains disjoint unions of polytopes that are pairwise disjoint.

            Return `False` otherwise.
            '''
            return False


        def vector_space(self):
            r'''
            Return the vector space over the provided field of the provided dimension.
            '''
            return VectorSpace(self.field(), self.dimension())

        def polyhedra(self):
            return Polyhedra(self.field(), self.dimension())

        @cached_method
        def point_set_category(self):
            return PointSets(self.field())

    class ElementMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """
        @abstract_method
        def polytopes(self):
            r'''Return the a mapping from labels to polytopes.'''
            pass

        def labels(self):
            r'''Return the collection of labels.'''
            return self.polytopes().keys()

        def polytope(self, label):
            r'''Return the polytope with the given label.'''
            return self.polytopes()[label]

        def is_finite(self):
            r"""
            Return whether this is a finite subdivision, which it is.
            """
            try:
                len(self.polytopes())
                return True
            except TypeError:
                # len attempts to return infinity which results in an error.
                return False

        @cached_method
        def point_set(self):
            r'''Construct the set of points in this disjoint union'''
            from pet_salon.point import PointSet
            return PointSet(self)

        def point(self, label, position, check=True):
            r'''Construct a points in this disjoint union from a `label` of a polytope and a `position` (vector) within it

            EXAMPLES::

                sage: from pet_salon import PolytopeUnions
                sage: from sage.geometry.polyhedron.constructor import Polyhedron
                sage: U = PolytopeUnions(2, QQ, finite=True)
                sage: union = U(Polyhedron(vertices=[(0,0), (1,0), (0,1)]))
                sage: union.point(0, (1/2, 1/3) )
                Point(0, (1/2, 1/3))
            '''
            pt = self.point_set()(label, position)
            if check:
                try:
                    pt._test_containment()
                except Exception:
                    raise ValueError('position is probably not within polytope')
            return pt

    class Finite(CategoryWithAxiom):
        r"""
        The axiom satisfied by finite subdivisions.

        EXAMPLES::

            sage: from pet_salon.union import PolytopeUnionsCategory
            sage: C = PolytopeUnionsCategory()
            sage: C.Finite()
            Category of finite disjoint polytope unions
        """
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self._fix_name()

        class ParentMethods:
            r"""
            Provides methods available to all parents of finite disjoint unions.
            """

        class ElementMethods:
            r"""
            Provides methods available to all finite disjoint unions.
            """
            def is_finite(self):
                r"""
                Return whether this is a finite subdivision, which it is.
                """
                return True

            def restrict(self, new_labels):
                r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

                The parameter `new_labels` should be a collection of the new labels.

                EXAMPLES::

                    sage: from pet_salon import PolytopeUnions, rectangle
                    sage: U = PolytopeUnions(2, QQ, finite=True, disjoint_images=True)
                    sage: union = U({
                    ....:     0: rectangle(QQ, 0, 1, 0, 1),
                    ....:     1: rectangle(QQ, 1, 2, 0, 1),
                    ....:     2: rectangle(QQ, 2, 3, 0, 1),
                    ....: })
                    sage: union
                    Disjoint union of 3 polyhedra in QQ^2
                    sage: res = union.restrict([0,2])
                    sage: res
                    Disjoint union of 2 polyhedra in QQ^2
                    sage: for label in res.labels():
                    ....:     print(label, union.polytope(label) == res.polytope(label))
                    0 True
                    2 True
                    sage: TestSuite(res).run()
                '''
                new_dict = {label:self.polytope(label) for label in new_labels}
                return self.parent(new_dict)

            @cached_method
            def volume(self, limit=None):
                return sum([p.volume() for _,p in self.polytopes().items()])

    class DisjointImages(CategoryWithAxiom):
        r"""
        The axiom satisfied by finite subdivisions.

        EXAMPLES::

            sage: from pet_salon.union import PolytopeUnionsCategory
            sage: C = PolytopeUnionsCategory()
            sage: C.DisjointImages()
            Category of disjoint polytope unions with disjoint images
        """
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self._fix_name()

        class ParentMethods:

            def has_disjoint_images(self):
                r'''Return `True` if this parent only contains disjoint unions of polytopes that are pairwise disjoint.

                Return `False` otherwise.
                '''
                return True

        class ElementMethods:
            def _test_disjointness(self, tester=None, limit=10):
                r'''
                Test that the polytopes have pairwise disjoint interior.

                If the union is finite, we test all pairs for overlap. If the union
                is finite we go up to the `limit` parameter (default: `10`).
                '''
                if self.is_finite():
                    polytopes = list(self.polytopes().items())
                    for i in range(len(polytopes)):
                        label1, p1 = polytopes[i]
                        for j in range(i+1, len(polytopes)):
                            label2, p2 = polytopes[j]
                            assert p1.intersection(p2).volume() == 0, \
                                f'Polytope {label1} and polytope {label2} have intersecting interiors.'

            def find(self, position, all=False, limit=None):
                r'''
                Find a polytope containing the position (point).

                By default, we return the pair `(label, polytope)` associated to the
                first polytope found containing the point. If none is found `None` is
                returned.

                Since the polytopes only have disjoint interiors, it is possible
                that more than one polytope contains the position. To see all the polytopes,
                set the parameter `all=True`, then instead a generator is returned that
                iterates through all the polytopes containing the point. This option is
                (currently) only possible if the union is finite.

                For infinite unions, there is a `limit` parameter which describes how many
                polytopes to check before giving up. The default limit is available from
                the module level method `get_find_limit()` and can be changed with
                `set_find_limit(new_limit)`.

                The implementation here just iterates through all polyhedra in the union,
                checking for containment. This method should be overriden by a more
                efficient algorithm in the infinite case and in the case of large
                finite unions.

                EXAMPLES::

                    sage: from pet_salon import PolytopeUnions
                    sage: U = PolytopeUnions(2, QQ, finite=True, disjoint_images=True)
                    sage: union = U.an_element()
                    sage: pt = union.polytope(0).intersection(union.polytope(1)).center()
                    sage: pt
                    (1, 0)
                    sage: for label,polytope in union.find(pt, all=True):
                    ....:     print(label)
                    0
                    1
                '''
                position = self.parent().vector_space()(position)
                if self.is_finite():
                    if all:
                        def find_all():
                            for pair in self.polytopes().items():
                                if position in pair[1]:
                                    yield pair
                        return find_all()
                    if limit:
                        raise ValueError('In a finite surface we do not allow limits in the find operation.')
                    for pair in self.polytopes().items():
                        if position in pair[1]:
                            return pair
                    return None # Failed to find any polytope containing the position.
                else:
                    if all:
                        raise NotImplemented('Currently can only find all in a finite union.')
                    if not limit:
                        limit = _find_limit
                    for pair,_ in zip(self.polytopes().items(), range(limit)):
                        if position in pair[1]:
                            return pair
                    return None # Failed to find any polytope containing the position within the limit.

            def point(self, label_or_position, position=None, check=True, all=False, limit=None):
                r'''Construct a points in this disjoint union from a `label` of a polytope and a `position` (vector) within it, or simply a position.

                EXAMPLES::

                    sage: from pet_salon import PolytopeUnions
                    sage: U = PolytopeUnions(2, QQ, finite=True, disjoint_images=True)
                    sage: union = U.an_element()
                    sage: pt = union.polytope(0).intersection(union.polytope(1)).center()
                    sage: pt
                    (1, 0)
                    sage: for pt in union.point(pt, all=True):
                    ....:     print(pt)
                    Point(0, (1, 0))
                    Point(1, (1, 0))
                '''
                if position is None:
                    if all:
                        P = self.point_set()
                        def point_generator():
                            for label,_ in self.find(label_or_position, all=True, limit=limit):
                                yield P(label, label_or_position)
                        return point_generator()
                    else:
                        found = self.find(label_or_position, all=False, limit=limit)
                        if found is None:
                            return None
                        else:
                            return self.point_set()(found[0], label_or_position)
                else:
                    assert not all, 'If a label and a position are provided, `all` must be False.'
                    pt = self.point_set()(label_or_position, position)
                    if check:
                        try:
                            pt._test_containment()
                        except Exception:
                            raise ValueError('position is probably not within polytope')
                    return pt


class PolytopeUnion(Element):
    def __init__(self, parent, mapping):
        r'''
        Construct a new Polytope union.

        The `parent` should be a `PolytopeUnions`, which specifies the `field`
        as well as the dimension. The mapping should send labels to polyhedra.
        '''
        self._mapping = mapping
        Element.__init__(self, parent)

    def polytopes(self):
        r'''Return the a mapping from labels to polytopes.'''
        return self._mapping

    def __eq__(self, other):
        if self is other:
            return True
        if not isinstance(other, PolytopeUnion):
            return False
        if self.parent() != other.parent():
            return False
        if self.is_finite() != other.is_finite():
            return False
        if self.is_finite():
            return self.polytopes() == other.polytopes()
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        if self.is_finite():
            return hash((self.parent(), frozenset(self.polytopes().items())))
        else:
            hash(id(self))

    def __repr__(self):
        s = str(self.parent().polyhedra())
        if self.is_finite():
            size = len(self.polytopes())
            return f'Disjoint union of {size} {s[0].lower()}{s[1:]}'
        else:
            return f'Disjoint union of infinitely many {s[0].lower()}{s[1:]}'

class PolytopeUnions(UniqueRepresentation, Parent):
    r'''
    Parent for domains of PETs of a given dimension that are defined over a given field.

    EXAMPLES::

    We can convert a single polyhedron to a union. It creates a union with a label of `0`.

        sage: from pet_salon import PolytopeUnions
        sage: from sage.geometry.polyhedron.constructor import Polyhedron
        sage: U = PolytopeUnions(2, QQ, finite=True)
        sage: TestSuite(U).run()
        sage: p0 = Polyhedron(vertices=[(1,0), (1,1), (-1,2)])
        sage: print(p0)
        A 2-dimensional polyhedron in ZZ^2 defined as the convex hull of 3 vertices
        sage: union = U(p0)
        sage: union
        Disjoint union of 1 polyhedra in QQ^2
        sage: TestSuite(union).run()
        sage: union.labels()
        dict_keys([0])
        sage: print(union.polytope(0))
        A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices

    An example of an infinite union:

        sage: from collections.abc import Mapping
        sage: from pet_salon import PolytopeUnions
        sage: U = PolytopeUnions(2, QQ, finite=False)
        sage: U
        Disjoint unions of polyhedra in dimension 2 over Rational Field with disjoint images
        sage: class ZZ2mapping(Mapping):
        ....:     def __init__(self, unions):
        ....:         from sage.rings.integer_ring import ZZ
        ....:         self._ZZ2 = ZZ.cartesian_product(ZZ)
        ....:         self._U = unions
        ....:     def __getitem__(self, key):
        ....:         if key in self._ZZ2:
        ....:             V = self._U.vector_space()
        ....:             v = V(key)
        ....:             return self._U.polyhedra()(Polyhedron(vertices=[v, v+V((1,0)), v+V((0,1)), v+V((1,1))]))
        ....:         else:
        ....:             raise KeyError
        ....:     def __iter__(self):
        ....:         return self._ZZ2.__iter__()
        ....:     def __len__(self):
        ....:         return infinity
        ....:
        sage: mapping = ZZ2mapping(U)
        sage: print(mapping[(3,4)])
        A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 4 vertices
        sage: union = U(mapping)
        sage: union
        Disjoint union of infinitely many polyhedra in QQ^2
        sage: TestSuite(union).run(skip=['_test_pickling'])
    '''
    Element = PolytopeUnion

    def __init__(self, dimension, field, finite=True, disjoint_images=True):
        cat = PolytopeUnionsCategory()
        if finite:
            cat = cat.Finite()
        if disjoint_images:
            cat = cat.DisjointImages()
        Parent.__init__(self, category=cat)
        self._field = field
        self._n = dimension
        if disjoint_images:
            end = ' with disjoint images'
        else:
            end = ''
        if finite:
            self.rename(f'Finite disjoint unions of polyhedra in dimension {self._n} over {self.field()}{end}')
        else:
            self.rename(f'Disjoint unions of polyhedra in dimension {self._n} over {self.field()}{end}')

    def field(self):
        r"""
        Return the ring over which this subdivision is defined.
        """
        return self._field

    def __eq__(self, other):
        if not isinstance(other, PolytopeUnions):
            return False
        return self.dimension() == other.dimension() and self.field() == other.field()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.dimension(), self.field()))

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
            if isinstance(args[0], PolytopeUnion):
                if not args[0].is_finite():
                    raise ValueError('Conversion to finite union not implemented yet')
                d = {label:args[0].polytope(label) for label in args[0].labels()}
                return self.element_class(self, d)
            elif isinstance(args[0], Mapping):
                return self.element_class(self, args[0])
            else:
                # We assume that the object passed is a Polyhedron
                try:
                    p0 = self.polyhedra()(args[0])
                    return self.element_class(self, {0: p0})
                except TypeError:
                    raise ValueError('Conversion not implemented yet')

        raise ValueError('Unclear how creata a finite union from passed parameters')

    def _an_element_(self):
        if 'DisjointImages' in self.category().axioms():
            from sage.geometry.polyhedron.library import polytopes
            P = self.polyhedra()
            p0 = P(polytopes.hypercube(self.dimension()))
            v = copy(self.vector_space().zero())
            v[0] = 2
            p1 = P(polytopes.cross_polytope(self.dimension())) + v
            return self({0:p0, 1:p1})
        else:
            from sage.geometry.polyhedron.library import polytopes
            P = self.polyhedra()
            p0 = P(polytopes.hypercube(self.dimension()))
            p1 = P(polytopes.cross_polytope(self.dimension()))
            return self({0:p0, 1:p1})

_find_limit = 100

def get_find_limit():
    r'''Get the limit for number of polytopes to check in a `find` operation in an infinite polyhedral union.'''
    return _find_limit

def set_find_limit(new_limit):
    r'''Set the limit for number of polytopes to check in a `find` operation in an infinite polyhedral union.'''
    global _find_limit
    _find_limit = new_limit



