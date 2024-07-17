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

# Make 'Injective' and 'Surjective' axioms in Sage:
all_axioms += ('Injective', 'Surjective')

class ImmersionsCategory(Category):
    r"""
    The category of polyhedral subsets together with an embedding in an ambient polyhedral union.

    EXAMPLES::

        sage: from pet_salon.immersion import ImmersionsCategory
        sage: ImmersionsCategory()
        Category of immersions into a polytope union
    """
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of immersions into a polytope union')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.immersion import ImmersionsCategory
            sage: C = ImmersionsCategory()
            sage: C.super_categories()
            [Category of sets]
        """
        return [Sets()]

    class SubcategoryMethods:

        def Injective(self):
            r'''Return this category with 'Injective' added to the axioms.

            An immersion is injective if it is one-to-one when restricted to the interior of the polytopes.

            EXAMPLES::

                sage: from pet_salon.immersion import ImmersionsCategory
                sage: ImmersionsCategory().Injective()
                Category of embeddings into a polytope union
                sage: ImmersionsCategory().Surjective().Injective()
                Category of partitions of a polytope union
            '''
            return self._with_axiom('Injective')

        def Surjective(self):
            r'''Return this category with 'Surjective' added to the axioms.

            An immersion is injective if it maps onto the ambient polytope union.

            EXAMPLES::

                sage: from pet_salon.immersion import ImmersionsCategory
                sage: ImmersionsCategory().Surjective()
                Category of surjective immersions into a polytope union
                sage: ImmersionsCategory().Injective().Surjective()
                Category of partitions of a polytope union
            '''
            return self._with_axiom('Surjective')

        def description(self):
            r'''Return a string describing the type of maps'''
            return 'Immersion'

    class ParentMethods:

        @abstract_method
        def ambient_union(self):
            r'''Return the ambient polyhedral union. This is also the codomain of the immersion.'''
            pass

        def field(self):
            return self.ambient_union().parent().field()

        def dimension(self):
            return self.ambient_union().parent().dimension()


    class ElementMethods:
        @abstract_method
        def domain(self):
            r'''Return the domain of this immersion.'''
            pass

        @abstract_method
        def subunions(self):
            r'''
            Return a mapping sending an `ambient_label` to the restriction of the subunion to polytopes
            contained within the polytope with the provided `ambient_label`.
            '''
            pass

        @abstract_method
        def ambient_labels(self):
            r'''Return a mapping sending labels in the domain to labels in the ambient union.'''
            pass

        def __call__(self, subpt):
            r'''Return the image of the point under the inclusion into the ambient_union.

            EXAMPLES::

                sage: from pet_salon.immersion import Immersions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Immersions(union)
                sage: S
                Immersions into disjoint union of 1 polyhedra in QQ^2
                sage: su = S(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:           2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: su
                Immersion of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 polyhedra in QQ^2
                sage: pt = su.domain().point((2/3,1/4))
                sage: pt
                Point(2, (2/3, 1/4))
                sage: su(pt)
                Point(0, (2/3, 1/4))
            '''
            return self.parent().ambient_union().point(
                self.ambient_labels()[subpt.label()],
                subpt.position()
            )

        def preimage(self, point, all=False, limit=None):
            r'''
            Given a point in the ambient union, find a corresponding point in the domain.

            If `all` is set to `True` we return an iterator over all preimages.

            This method just passes the call to `find` from the appropriate domain.

            EXAMPLES::

                sage: from pet_salon.immersion import Immersions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Immersions(union)
                sage: S
                Immersions into disjoint union of 1 polyhedra in QQ^2
                sage: su = S(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:           2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: su
                Immersion of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 polyhedra in QQ^2
                sage: pt = union.point((4/5,1/3))
                sage: pt
                Point(0, (4/5, 1/3))
                sage: su.preimage(pt)
                Point(2, (4/5, 1/3))
            '''
            assert point.parent() == self.parent().ambient_union().point_set(), \
                'point must lie in the ambient union'
            subunion = self.subunions()[point.label()]
            return self.domain().point_set()(subunion.point(point.position()))

        def _test_containment(self, tester=None):
            r'''Raise an assertion error if a polytope from the domain is not contained within the
            claimed polytope in the ambient union.

            EXAMPLES::

                sage: from pet_salon.immersion import Immersions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Immersions(union)
                sage: S
                Immersions into disjoint union of 1 polyhedra in QQ^2
                sage: attempted_subunion = U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:                         2:rectangle(QQ,1/2,  2, 0, 1/2)})
                sage: attempted_subunion
                Disjoint union of 2 polyhedra in QQ^2
                sage: su = S(attempted_subunion,
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: attempted_subunion})
                sage: su
                Immersion of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 polyhedra in QQ^2
                sage: su._test_containment()
                Traceback (most recent call last):
                ...
                AssertionError...
            '''
            def check_pair(domain_label, ambient_label):
                domain_p = self.domain().polytope(domain_label)
                ambient_p = self.parent().ambient_union().polytope(ambient_label)
                assert is_subpolytope(ambient_p, domain_p), \
                    f'Immersion polytope with label {domain_label} is not contained within ambient polytope with label {ambient_label}'
            if self.domain().is_finite():
                for pair in self.ambient_labels().items():
                    check_pair(*pair)
            else:
                for pair,_ in zip(self.ambient_labels().items(), range(20)):
                    check_pair(*pair)

        def _test_domain(self, tester=None, limit=10):
            r'''Run all PolytopeUnion tests on both the whole domain and the subunions associated to ambient labels.

            EXAMPLES::

                sage: from pet_salon.immersion import Embeddings
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: Udi = PolytopeUnions(2, QQ, disjoint_images=True)
                sage: U = PolytopeUnions(2, QQ, disjoint_images=False)
                sage: union = Udi({0: rectangle(QQ,0,1,0,1)})
                sage: E = Embeddings(union)
                sage: E
                Embeddings into disjoint union of 1 polyhedra in QQ^2
                sage: attempted_subunions = {1:rectangle(QQ,   0,1/2, 0, 1/2),
                ....:                               2:rectangle(QQ,   0,  1, 0, 1/2)}
                sage: su = E(U(attempted_subunions),
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: Udi(attempted_subunions)})
                sage: su
                Embedding of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 polyhedra in QQ^2
                sage: su._test_disjoint_images()
                sage: su._test_domain()
                Traceback (most recent call last):
                ...
                AssertionError: The subunion associated to ambient label 0 failed a test...
            '''
            try:
                TestSuite(self.domain()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The domain failed a test: {e}')
            if length(self.subunions()) < infinity:
                for ambient_label, subunion in self.subunions().items():
                    try:
                        TestSuite(subunion).run(catch=False, raise_on_failure=True)
                    except Exception as e:
                        raise AssertionError(f'The subunion associated to ambient label {ambient_label} failed a test: {e}')

    class Injective(CategoryWithAxiom):
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self.rename(f'Category of embeddings into a polytope union')

        class SubcategoryMethods:

            def description(self):
                r'''Return a string describing the type of maps'''
                return 'Embedding'

        class ElementMethods:

            def _test_disjoint_images(self, tester=None, limit=20):
                r'''Test if the subunions associated to ambient labels have disjoint images.

                This just checks the axiom. The test `_test_subunion` will check that the subunions
                consist of pairwise disjoint polytopes.

                EXAMPLES::

                    sage: from pet_salon.immersion import Embeddings
                    sage: from pet_salon import PolytopeUnions, rectangle
                    sage: U = PolytopeUnions(2, QQ, disjoint_images=False)
                    sage: union = U({0: rectangle(QQ,0,1,0,1)})
                    sage: E = Embeddings(union)
                    sage: E
                    Embeddings into disjoint union of 1 polyhedra in QQ^2
                    sage: attempted_domain = U({1:rectangle(QQ,   0,1/2, 0, 1/2),
                    ....:                         2:rectangle(QQ, 1/2,  1, 0, 1/2)})
                    sage: attempted_domain
                    Disjoint union of 2 polyhedra in QQ^2
                    sage: su = E(attempted_domain,
                    ....:        { 1: 0, 2:0 }, # mapping to ambient label
                    ....:        { 0: attempted_domain})
                    sage: su
                    Embedding of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 polyhedra in QQ^2
                    sage: su._test_disjoint_images()
                    Traceback (most recent call last):
                    ...
                    AssertionError: The subunion associated to ambient label 0 does not have the disjoint images axiom
                '''
                if length(self.subunions()) < infinity:
                    for ambient_label, subunion in self.subunions().items():
                        assert subunion.parent().has_disjoint_images(), \
                            f'The subunion associated to ambient label {ambient_label} does not have the disjoint images axiom'
                        # Removed because this is tested by `_test_subunion`.
                        #try:
                        #    subunion._test_disjointness()
                        #except AssertionError:
                        #    raise AssertionError(f'The subunion associated to ambient label {ambient_label} does not have the disjoint images despite the axiom')
                else:
                    for (ambient_label, subunion),_ in zip(self.subunions().items()), range(limit):
                        assert subunion.parent().has_disjoint_images(), \
                            f'The subunion associated to ambient label {ambient_label} does not have the disjoint images axiom'

    class Surjective(CategoryWithAxiom):
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self.rename(f'Category of surjective immersions into a polytope union')

        class SubcategoryMethods:

            def description(self):
                r'''Return a string describing the type of maps'''
                return 'Surjective embedding'

        class ElementMethods:

            def _test_surjectivity(self, tester=None, limit=20):
                r'''We check surjectivity at the level of the labels.'''
                value = length(self.subunions())
                assert value <= length(self.parent().ambient_union().labels()), \
                    'The mapping is not well defined: There are labels in subunions that do not appear in the ambient union'
                assert value >= length(self.parent().ambient_union().labels()), \
                    'The surjective immersion misses at least one ambient label'
                if value < infinity:
                    assert self.subunions().keys() == self.parent().ambient_union().labels(), \
                        'The support of the subunion mapping is different from the collection of all ambient labels: The sets are different'
                else:
                    for ambient_label,_ in zip(self.parent().ambient_union().labels(), range(limit)):
                        assert ambient_label in self.subunions(), \
                            f'Ambient label {ambient_label} does not appear in the subunion mapping'

            def _test_volume(self, tester=None, limit=20):
                r'''This test checks to see if the subunion of domain polytopes mapping into an ambient
                polytope have volume that is at least as large as the ambient polytope.

                This test only works for finite subunions. If there are infinitely many ambient labels,
                then we test `limit` many.

                EXAMPLES::
                    sage: from pet_salon import PolytopeUnions, rectangle
                    sage: from pet_salon.immersion import Partitions
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
                    Partition of disjoint union of 1 polyhedra in QQ^2 into 3 subpolytopes
                    sage: TestSuite(partition).run()
                    Failure in _test_volume:
                    ...
                    The following tests failed: _test_volume
                '''
                def test_pair(ambient_label, subunion):
                    if subunion.is_finite():
                            assert subunion.volume() >= self.parent().ambient_union().polytope(ambient_label).volume(), \
                                f'The partition axiom is violated: The volume of the subunion associated to the ambient label {ambient_label} is not at least as large as the ambient polytope\'s volume'
                if length(self.subunions()) < infinity:
                    for pair in self.subunions().items():
                        test_pair(*pair)
                else:
                    for pair,_ in zip(self.subunions().items(), range(limit)):
                        test_pair(*pair)

        class Injective(CategoryWithAxiom):
            r'''This is the category of paritions of a polytope union'''
            def __init__(self, *args, **options):
                CategoryWithAxiom.__init__(self, *args, **options)
                self.rename(f'Category of partitions of a polytope union')

            class SubcategoryMethods:

                def description(self):
                    r'''Return a string describing the type of maps'''
                    return 'Partition'

class Immersion(Element):
    def __init__(self, parent, domain, ambient_labels_mapping=None, subunions=None, name=None):
        self._domain = domain
        if not ambient_labels_mapping:
            assert 'DisjointImages' in parent.ambient_union().parent().category().axioms(), \
                'ambient_labels_mapping must be defined if the containing PolytopeUnion does not have disjoint images'
            assert parent.ambient_union().is_finite(), \
                'ambient_labels_mapping must be defined if the containing PolytopeUnion is not finite'
            assert domain.is_finite(), \
                'ambient_labels_mapping must be defined if `domain` is not finite'
            ambient_labels_mapping = {}
            for label, polytope in domain.polytopes().items():
                center = polytope.center()
                pair = parent.ambient_union().find(center)
                if not pair:
                    raise ValueError(f'The subunion polytope with label {label} is not contained in a polytope from the ambient union.')
                ambient_labels_mapping[label] = pair[0]
            #print('ambient_labels_mapping', ambient_labels_mapping)
        if not subunions:
            assert domain.is_finite(), \
                'subunions must be defined if `domain` is not finite'
            assert parent.ambient_union().is_finite(), \
                'subunions must be defined if the containing PolytopeUnion is not finite'
            ambient_label_to_list = {}
            for label, ambient_label in ambient_labels_mapping.items():
                if ambient_label in ambient_label_to_list:
                    ambient_label_to_list[ambient_label].append(label)
                else:
                    ambient_label_to_list[ambient_label] = [label]
            #print('ambient_label_to_list', ambient_label_to_list)
            subunions = {}
            for ambient_label, lst in ambient_label_to_list.items():
                subunions[ambient_label] = domain.restrict(lst)
        self._domain = domain
        self._ambient_labels_mapping = ambient_labels_mapping
        self._subunions = subunions
        Element.__init__(self, parent)
        if name:
            self.rename(name)
        else:
            ambient_name = repr(parent.ambient_union())
            axioms = parent.category().axioms()
            if 'Injective' in axioms and 'Surjective' in axioms:
                if domain.is_finite():
                    number = len(domain.polytopes())
                else:
                    number = '∞ly many'
                self.rename(f'Partition of {ambient_name[0].lower()}{ambient_name[1:]} into {number} subpolytopes')
            else:
                start = parent.category().description()
                domain_name = repr(domain)
                self.rename(f'{parent.category().description()} of {domain_name[0].lower()}{domain_name[1:]} into {ambient_name[0].lower()}{ambient_name[1:]}')

    def domain(self):
        r'''Return the domain of this immersion.'''
        return self._domain

    def subunions(self):
        r'''
        Return a mapping sending an `ambient_label` to the restriction of the subunion to polytopes
        contained within the polytope with the provided `ambient_label`.
        '''
        return self._subunions

    def ambient_labels(self):
        r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
        return self._ambient_labels_mapping

    def __eq__(self, other):
        if self is other:
            return True
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        if self.domain() != other.domain():
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
            return hash((self.parent(), self.domain()))
        else:
            if self.ambient_union().is_finite():
                ambient_labels = frozenset((label,ambient_label) for label,ambient_label in self.ambient_labels().items())
                return hash((self.parent(), self.domain(), ambient_labels))
            else:
                return id(self)

class Immersions(Parent):
    Element = Immersion

    def __init__(self, ambient_union, injective=False, surjective=False):
        assert ambient_union.parent().category().is_subcategory(PolytopeUnionsCategory()), \
            'ambient_union must be a PolytopeUnion'
        cat = ImmersionsCategory()
        start = 'Immersions into'
        if injective:
            start = 'Embeddings into'
            cat = cat.Injective()
        if surjective:
            cat = cat.Surjective()
            if injective:
                start = 'Partitions of'
            else:
                start = 'Surjective immersions into'
        self._ambient_union = ambient_union
        Parent.__init__(self, category=cat)
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

            sage: from pet_salon.immersion import Partitions
            sage: from pet_salon import PolytopeUnions
            sage: U = PolytopeUnions(2, QQ)
            sage: union = U.an_element()
            sage: union
            Disjoint union of 2 polyhedra in QQ^2
            sage: S = Partitions(union)
            sage: p = S.trivial()
            sage: p
            Partition of disjoint union of 2 polyhedra in QQ^2 into 2 subpolytopes
            sage: p.domain() == union
            True
            sage: p.ambient_labels()
            {0: 0, 1: 1}
            sage: pt = p.domain().point((0,0))
            sage: pt
            Point(0, (0, 0))
            sage: pt == p.preimage(pt)
            True
            sage: pt == p.inclusion(pt)
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

def Embeddings(ambient_union):
    r'''Construct the collection of embeddings into the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import Embeddings
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1))
        sage: union
        Disjoint union of 1 polyhedra in QQ^2
        sage: E = Embeddings(union)
        sage: E
        Embeddings into disjoint union of 1 polyhedra in QQ^2
        sage: TestSuite(E).run()
        sage: e = E(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....: }))
        sage: e
        Embedding of disjoint union of 3 polyhedra in QQ^2 into disjoint union of 1 polyhedra in QQ^2
        sage: TestSuite(e).run()
    '''
    return Immersions(ambient_union, injective=True, surjective=False)

def Partitions(ambient_union):
    r'''Construct the collection of partitions of the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import Partitions
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
        Partition of disjoint union of 1 polyhedra in QQ^2 into 4 subpolytopes
        sage: TestSuite(partition).run()
    '''
    return Immersions(ambient_union, injective=True, surjective=True)
