from collections.abc import Mapping

from sage.categories.all import Sets
from sage.categories.category import Category
from sage.categories.category_with_axiom import CategoryWithAxiom, all_axioms
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.sage_unittest import TestSuite
from sage.rings.infinity import infinity
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.collection import identity_mapping, function_mapping, length
from pet_salon.polytope import is_subpolytope
from pet_salon.union import PolytopeUnions, PolytopeUnionsCategory

# Make 'Partition' an axiom in Sage:
all_axioms += ("Partition",)

class SubunionsCategory(Category):
    r"""
    The category of polyhedral subsets together with an embedding in an ambient polyhedral union.

    EXAMPLES::

        sage: from pet_salon.subunion import SubunionsCategory
        sage: SubunionsCategory()
        Category of subsets of a polytope union
    """
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of subsets of a polytope union')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.point import PointSetsCategory
            sage: C = PointSetsCategory()
            sage: C.super_categories()
            [Category of sets]

        """
        return [Sets()]

    class SubcategoryMethods:

        def Partition(self):
            r'''We say a PolytopeUnion has Disjoint images if the polytopes, viewed as subsets of the vector space containing them, have disjoint interiors.

            This will make available the `find` method.'''
            return self._with_axiom('Partition')

    class ParentMethods:

        @abstract_method
        def ambient_union(self):
            r'''Return the ambient polyhedral union.'''
            pass

        def field(self):
            return self.ambient_union().parent().field()

        def dimension(self):
            return self.ambient_union().parent().dimension()


    class ElementMethods:
        @abstract_method
        def subunion_mapping(self):
            r'''
            Return a mapping sending an `ambient_label` to the restriction of the subunion to polytopes
            contained within the polytope with the provided `ambient_label`.
            '''
            pass

        @abstract_method
        def subunion(self, label=None):
            r'''With no parameters, return the subunion. When a label in the ambient union is provided,
            return the subunion of polytopes contained within associated polytope.'''
            pass

        @abstract_method
        def ambient_labels(self):
            r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
            pass

        def inclusion(self, subpt):
            r'''Return the image of the point under the inclusion into the ambient_union.

            EXAMPLES::

                sage: from pet_salon.subunion import Subunions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Subunions(union)
                sage: S
                Subunions contained in disjoint union of 1 polyhedra in QQ^2
                sage: su = S(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:           2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: su
                Subunion of disjoint union of 1 polyhedra in QQ^2 consisting of 2 polytopes
                sage: pt = su.subunion().point((2/3,1/4))
                sage: pt
                Point(2, (2/3, 1/4))
                sage: su.inclusion(pt)
                Point(0, (2/3, 1/4))
            '''
            return self.parent().ambient_union().point(
                self.ambient_labels()[subpt.label()],
                subpt.position()
            )

        def preimage(self, point, all=False, limit=None):
            r'''
            Given a point in the ambient union, find a corresponding point in the subunion.
            This method just passes the call to `find` from the appropriate subunion.


            EXAMPLES::

                sage: from pet_salon.subunion import Subunions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Subunions(union)
                sage: S
                Subunions contained in disjoint union of 1 polyhedra in QQ^2
                sage: su = S(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:           2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: su
                Subunion of disjoint union of 1 polyhedra in QQ^2 consisting of 2 polytopes
                sage: pt = union.point((4/5,1/3))
                sage: pt
                Point(0, (4/5, 1/3))
                sage: su.preimage(pt)
                Point(2, (4/5, 1/3))
            '''
            assert point.parent() == self.parent().ambient_union().point_set(), \
                'point must lie in the ambient union'
            subunion = self.subunion(point.label())
            return self.subunion().point_set()(subunion.point(point.position()))

        def _test_containment(self, tester=None):
            r'''Raise an assertion error if a polytope from the subunion is not contained within the
            claimed polytope in the ambient union.

            EXAMPLES::

                sage: from pet_salon.subunion import Subunions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Subunions(union)
                sage: S
                Subunions contained in disjoint union of 1 polyhedra in QQ^2
                sage: attempted_subunion = U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:                         2:rectangle(QQ,1/2,  2, 0, 1/2)})
                sage: attempted_subunion
                Disjoint union of 2 polyhedra in QQ^2
                sage: su = S(attempted_subunion,
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: attempted_subunion})
                sage: su
                Subunion of disjoint union of 1 polyhedra in QQ^2 consisting of 2 polytopes
                sage: su._test_containment()
                Traceback (most recent call last):
                ...
                AssertionError...
            '''
            def check_pair(subunion_label, ambient_label):
                subunion_p = self.subunion().polytope(subunion_label)
                ambient_p = self.parent().ambient_union().polytope(ambient_label)
                assert is_subpolytope(ambient_p, subunion_p), \
                    f'Subunion polytope with label {subunion_label} is not contained within ambient polytope with label {ambient_label}'
            if self.subunion().is_finite():
                for pair in self.ambient_labels().items():
                    check_pair(*pair)
            else:
                for pair,_ in zip(self.ambient_labels().items(), range(20)):
                    check_pair(*pair)

        def _test_subunion(self, tester=None, limit=10):
            r'''Run all PolytopeUnion tests on both the whole subunion and subunions associated to ambient labels.

            EXAMPLES::

                sage: from pet_salon.subunion import Subunions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: Udi = PolytopeUnions(2, QQ, disjoint_images=True)
                sage: U = PolytopeUnions(2, QQ, disjoint_images=False)
                sage: union = Udi({0: rectangle(QQ,0,1,0,1)})
                sage: S = Subunions(union)
                sage: S
                Subunions contained in disjoint union of 1 polyhedra in QQ^2
                sage: attempted_subunion_mapping = {1:rectangle(QQ,   0,1/2, 0, 1/2),
                ....:                               2:rectangle(QQ,   0,  1, 0, 1/2)}
                sage: su = S(U(attempted_subunion_mapping),
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: Udi(attempted_subunion_mapping)})
                sage: su
                Subunion of disjoint union of 1 polyhedra in QQ^2 consisting of 2 polytopes
                sage: su._test_disjoint_images()
                sage: su._test_subunion()
                Traceback (most recent call last):
                ...
                AssertionError: The subunion associated to ambient label 0 failed a test...
            '''
            try:
                TestSuite(self.subunion()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The whole subunion failed a test: {e}')
            if length(self.subunion_mapping()) < infinity:
                for ambient_label, restricted_subunion in self.subunion_mapping().items():
                    try:
                        TestSuite(restricted_subunion).run(catch=False, raise_on_failure=True)
                    except Exception as e:
                        raise AssertionError(f'The subunion associated to ambient label {ambient_label} failed a test: {e}')

        def _test_disjoint_images(self, tester=None, limit=20):
            r'''Test if the restricted subunions associated to ambient labels have disjoint images.

            This just checks the axiom. The test `_test_subunion` should check the whole subunion and
            the restricted subunions.

            EXAMPLES::

                sage: from pet_salon.subunion import Subunions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ, disjoint_images=False)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Subunions(union)
                sage: S
                Subunions contained in disjoint union of 1 polyhedra in QQ^2
                sage: attempted_subunion = U({1:rectangle(QQ,   0,1/2, 0, 1/2),
                ....:                         2:rectangle(QQ, 1/2,  1, 0, 1/2)})
                sage: attempted_subunion
                Disjoint union of 2 polyhedra in QQ^2
                sage: su = S(attempted_subunion,
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: attempted_subunion})
                sage: su
                Subunion of disjoint union of 1 polyhedra in QQ^2 consisting of 2 polytopes
                sage: su._test_disjoint_images()
                Traceback (most recent call last):
                ...
                AssertionError: The restricted subunion associated to ambient label 0 does not have the disjoint images axiom
            '''
            if length(self.subunion_mapping()) < infinity:
                for ambient_label, restricted_subunion in self.subunion_mapping().items():
                    assert restricted_subunion.parent().has_disjoint_images(), \
                        f'The restricted subunion associated to ambient label {ambient_label} does not have the disjoint images axiom'
                    # Removed because this is tested by `_test_subunion`.
                    #try:
                    #    restricted_subunion._test_disjointness()
                    #except AssertionError:
                    #    raise AssertionError(f'The restricted subunion associated to ambient label {ambient_label} does not have the disjoint images despite the axiom')
            else:
                for (ambient_label, restricted_subunion),_ in zip(self.subunion_mapping().items()), range(limit):
                    assert restricted_subunion.parent().has_disjoint_images(), \
                        f'The restricted subunion associated to ambient label {ambient_label} does not have the disjoint images axiom'

    class Partition(CategoryWithAxiom):

        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self.rename(f'Category of partitions of a polytope union')

        class ElementMethods:

            def _test_bijectivity(self, tester=None, limit=20):
                r'''We check to see if the image of the inclusion mapping (from the subunion into the
                ambient union) includes points in all polytopes in the ambient union. (When combined
                with the volume test and the other tests from the Subunion class, this ensures that
                the inclusion is a bijection (almost everywhere).'''
                value = length(self.subunion_mapping())
                assert value == length(self.parent().ambient_union().labels()), \
                    'The support of the subunion mapping is different from the collection of all ambient labels because these collections have distinct cardinalities'
                if value < infinity:
                    assert self.subunion_mapping().keys() == self.parent().ambient_union().labels(), \
                        'The support of the subunion mapping is different from the collection of all ambient labels: The sets are different'
                else:
                    for ambient_label,_ in zip(self.parent().ambient_union().labels(), range(limit)):
                        assert ambient_label in self.subunion_mapping(), \
                            f'Ambient label {ambient_label} does not appear in the subunion mapping'

            def _test_volume(self, tester=None, limit=20):
                r'''This test checks to see if each polytope in the ambient union is divided into a
                collection of polytopes with the same total volume. This only works if this division is
                finite.

                EXAMPLES::
                    sage: from pet_salon import PolytopeUnions, rectangle
                    sage: from pet_salon.subunion import Partitions
                    sage: U = PolytopeUnions(2, QQ)
                    sage: union = U(rectangle(QQ, 0, 1, 0, 1))
                    sage: union
                    Disjoint union of 1 polyhedra in QQ^2
                    sage: P = Partitions(union)
                    sage: partition = P(U({
                    ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
                    ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
                    ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
                    ....: }))
                    sage: partition
                    Partition of disjoint union of 1 polyhedra in QQ^2 consisting of 3 polytopes
                    sage: TestSuite(partition).run()
                    Failure in _test_volume:
                    ...
                    The following tests failed: _test_volume
                '''
                def test_pair(ambient_label, restricted_subunion):
                    if restricted_subunion.is_finite():
                            assert restricted_subunion.volume() == self.parent().ambient_union().polytope(ambient_label).volume(), \
                                f'The partition axiom is violated: The volume of the restricted subunion associated to the ambient label {ambient_label} is not equal to the ambient polytope with that label'
                if length(self.subunion_mapping()) < infinity:
                    for pair in self.subunion_mapping().items():
                        test_pair(*pair)
                else:
                    for pair,_ in zip(self.subunion_mapping().items(), range(limit)):
                        test_pair(*pair)

class Subunion(Element):
    def __init__(self, parent, whole_subunion, ambient_labels_mapping=None, subunion_mapping=None):
        self._whole_subunion = whole_subunion
        if not ambient_labels_mapping:
            assert 'DisjointImages' in parent.ambient_union().parent().category().axioms(), \
                'ambient_labels_mapping must be defined if the containing PolytopeUnion does not have disjoint images'
            assert parent.ambient_union().is_finite(), \
                'ambient_labels_mapping must be defined if the containing PolytopeUnion is not finite'
            assert whole_subunion.is_finite(), \
                'ambient_labels_mapping must be defined if `whole_subunion` is not finite'
            ambient_labels_mapping = {}
            for label, polytope in whole_subunion.polytopes().items():
                center = polytope.center()
                pair = parent.ambient_union().find(center)
                if not pair:
                    raise ValueError(f'The subunion polytope with label {label} is not contained in a polytope from the ambient union.')
                ambient_labels_mapping[label] = pair[0]
            #print('ambient_labels_mapping', ambient_labels_mapping)
        if not subunion_mapping:
            assert whole_subunion.is_finite(), \
                'subunion_mapping must be defined if `whole_subunion` is not finite'
            assert parent.ambient_union().is_finite(), \
                'subunion_mapping must be defined if the containing PolytopeUnion is not finite'
            ambient_label_to_list = {}
            for label, ambient_label in ambient_labels_mapping.items():
                if ambient_label in ambient_label_to_list:
                    ambient_label_to_list[ambient_label].append(label)
                else:
                    ambient_label_to_list[ambient_label] = [label]
            #print('ambient_label_to_list', ambient_label_to_list)
            subunion_mapping = {}
            for ambient_label, lst in ambient_label_to_list.items():
                subunion_mapping[ambient_label] = whole_subunion.restrict(lst)
        self._whole_subunion = whole_subunion
        self._ambient_labels_mapping = ambient_labels_mapping
        self._subunion_mapping = subunion_mapping
        Element.__init__(self, parent)
        if 'Partition' in parent.category().axioms():
            start = 'Partition'
        else:
            start = 'Subunion'
        union_name = repr(parent.ambient_union())
        if whole_subunion.is_finite():
            number = len(whole_subunion.polytopes())
        else:
            number = '∞ly many'
        self.rename(f'{start} of {union_name[0].lower()}{union_name[1:]} consisting of {number} polytopes')

    def subunion_mapping(self):
        r'''
        Return a mapping sending an `ambient_label` to the restriction of the subunion to polytopes
        contained within the polytope with the provided `ambient_label`.
        '''
        return self._subunion_mapping

    def subunion(self, label=None):
        r'''With no parameters, return the subunion. When a label in the ambient union is provided,
        return the subunion of polytopes contained within associated polytope.'''
        if label is None:
            return self._whole_subunion
        else:
            return self._subunion_mapping[label]

    def ambient_labels(self):
        r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
        return self._ambient_labels_mapping

    def __eq__(self, other):
        if self is other:
            return True
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        if self.subunion() != other.subunion():
            return False
        if 'DisjointImages' in self.parent().ambient_union().parent().category().axioms():
            # Nothing more to check
            return True
        try:
            len(self.ambient_labels())
            self_ambient_labels_finite = True
        except TypeError:
            self_ambient_labels_finite = False
        try:
            len(other.ambient_labels())
            other_ambient_labels_finite = True
        except TypeError:
            other_ambient_labels_finite = False
        if self_ambient_labels_finite != other_ambient_labels_finite:
            return False
        self_al = self.ambient_labels()
        other_al = other.ambient_labels()
        if self_ambient_labels_finite:
            for label in self.ambient_labels():
                if self_al[label] != other_al[label]:
                    return False
            return True
        else:
            # hopeless
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    @cached_method
    def __hash__(self):
        if 'DisjointImages' in self.parent().ambient_union().parent().category().axioms():
            return hash((self.parent(), self.subunion()))
        else:
            if self.ambient_union().is_finite():
                ambient_labels = frozenset((label,ambient_label) for label,ambient_label in self.ambient_labels().items())
                return hash((self.parent(), self.subunion(), ambient_labels))
            else:
                return id(self)

class Subunions(Parent):
    Element = Subunion

    def __init__(self, ambient_union, partitions=False):
        assert ambient_union.parent().category().is_subcategory(PolytopeUnionsCategory()), \
            'ambient_union must be a PolytopeUnion'
        if partitions:
            cat = category=SubunionsCategory().Partition()
            start = 'Partitions of'
        else:
            cat = category=SubunionsCategory()
            start = 'Subunions contained in'
        Parent.__init__(self, category=cat)
        self._ambient_union = ambient_union
        union_name = repr(ambient_union)
        self.rename(f'{start} {union_name[0].lower()}{union_name[1:]}')

    def ambient_union(self):
        return self._ambient_union

    def __eq__(self, other):
        if not hasattr(other, 'category'):
            return False
        if not other.category().is_subcategory(self.category()):
            return False
        return self.ambient_union() == other.ambient_union()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.category(), self.ambient_union()))

    def restriction(self, ambient_label_collection):
        if 'Partition' in self.category().axioms() and ambient_label_collection != self.ambient_union().labels():
            raise ValueError('The only restriction that is also a Partition is the trivial one')
        U = PolytopeUnions(self.dimension(), self.field(), finite=True, disjoint_images=True)
        return self(self.ambient_union().restrict(ambient_label_collection),
                    identity_mapping(ambient_label_collection),
                    function_mapping(ambient_label_collection,
                        lambda ambient_label:U({ambient_label: self.ambient_union().polytope(ambient_label)})))

    def trivial(self):
        r'''Construct the trivial subunion (where the subunion is equal to the ambient union).

        EXAMPLES:

            sage: from pet_salon.subunion import Subunions
            sage: from pet_salon import PolytopeUnions
            sage: U = PolytopeUnions(2, QQ)
            sage: union = U.an_element()
            sage: union
            Disjoint union of 2 polyhedra in QQ^2
            sage: S = Subunions(union)
            sage: su = S.trivial()
            sage: su
            Subunion of disjoint union of 2 polyhedra in QQ^2 consisting of 2 polytopes
            sage: su.subunion() == union
            True
            sage: su.ambient_labels()
            {0: 0, 1: 1}
            sage: pt = su.subunion().point((0,0))
            sage: pt
            Point(0, (0, 0))
            sage: pt == su.preimage(pt)
            True
            sage: pt == su.inclusion(pt)
            True
        '''
        return self.restriction(self.ambient_union().labels())

    def _element_constructor_(self, *args, **kwds):
        #print(f'Called element_constructor with args={args}')
        if len(args)==1:
            if hasattr(args[0], 'parent') and callable(args[0].parent) and \
                hasattr(args[0].parent(), 'category') and callable(args[0].parent().category) and \
                args[0].parent().category().is_subcategory(PolytopeUnionsCategory()):
                # arg[0] is a PolytopeUnion
                assert self.field() == args[0].parent().field(), \
                    'Currently the subunion must have the same base field as the ambient_union.'
                return self.element_class(self, args[0])
        if len(args) in [2,3]:
            return self.element_class(self, *args)
        raise NotImplementedError()

    def _an_element_(self):
        return self.trivial()

def Partitions(ambient_union):
    r'''Construct the collection of partitions of the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.subunion import Partitions
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1))
        sage: union
        Disjoint union of 1 polyhedra in QQ^2
        sage: P = Partitions(union)
        sage: P
        Partitions of disjoint union of 1 polyhedra in QQ^2
        sage: TestSuite(P).run()
        sage: partition = P(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....:     4: rectangle(QQ, 1/2,   1, 1/2,   1),
        ....: }))
        sage: partition
        Partition of disjoint union of 1 polyhedra in QQ^2 consisting of 4 polytopes
        sage: TestSuite(partition).run()
    '''
    return Subunions(ambient_union, partitions=True)
