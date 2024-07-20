# ********************************************************************
#  This file is part of pet-salon.
#
#        Copyright (C) 2024 W. Patrick Hooper
#
#  sage-flatsurf is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 2 of the License, or
#  (at your option) any later version.
#
#  sage-flatsurf is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with sage-flatsurf. If not, see <https://www.gnu.org/licenses/>.
# ********************************************************************

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

from .collection import identity_mapping, function_mapping, length, mapping_composition
from .polytope import is_subpolytope
from .union import PolytopeUnions, PolytopeUnionsCategory

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
                Category of surjective embeddings into a polytope union
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
                Category of surjective embeddings into a polytope union
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

        @abstract_method
        def with_different_axioms(self, injective=False, surjective=False):
            r'''Return a parent with the provided axioms.'''
            pass

        @abstract_method
        def with_different_union(self, new_ambient_union):
            pass

        def field(self):
            return self.ambient_union().parent().field()

        def dimension(self):
            return self.ambient_union().parent().dimension()

        def is_injective(self):
            return False

        def is_surjective(self):
            return False

        @cached_method
        def piecewise_affine_maps(self):
            from .affine import PiecewiseAffineMaps
            return PiecewiseAffineMaps(self.dimension(), self.field())


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

        def codomain(self):
            r'''Return the codomain which is also the ambient union.'''
            return self.parent().ambient_union()

        def __call__(self, subpt):
            r'''Return the image of the point under the inclusion into the ambient_union.

            EXAMPLES::

                sage: from pet_salon.immersion import Immersions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Immersions(union)
                sage: S
                Immersions into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: su = S(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:           2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: su
                Immersion of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
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

                sage: from pet_salon.immersion import Embeddings
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: E = Embeddings(union)
                sage: E
                Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: e = E(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:          2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: e
                Embedding of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: pt = union.point((4/5,1/3))
                sage: pt
                Point(0, (4/5, 1/3))
                sage: e.preimage(pt)
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
                Immersions into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: attempted_subunion = U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:                         2:rectangle(QQ,1/2,  2, 0, 1/2)})
                sage: attempted_subunion
                Disjoint union of 2 nonoverlapping polyhedra in QQ^2
                sage: su = S(attempted_subunion,
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: attempted_subunion})
                sage: su
                Immersion of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
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
                sage: Udi = PolytopeUnions(2, QQ, nonoverlapping=True)
                sage: U = PolytopeUnions(2, QQ, nonoverlapping=False)
                sage: union = Udi({0: rectangle(QQ,0,1,0,1)})
                sage: E = Embeddings(union)
                sage: E
                Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: attempted_subunions = {1:rectangle(QQ,   0,1/2, 0, 1/2),
                ....:                               2:rectangle(QQ,   0,  1, 0, 1/2)}
                sage: su = E(U(attempted_subunions),
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: Udi(attempted_subunions)})
                sage: su
                Embedding of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: su._test_nonoverlapping()
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

        class ParentMethods:

            def is_injective(self):
                return True

        class ElementMethods:

            def _test_nonoverlapping(self, tester=None, limit=20):
                r'''Test that the subunions associated to ambient labels are nonoverlapping.

                This just checks the axiom. The test `_test_subunion` will check that the subunions
                consist of pairwise disjoint polytopes.

                EXAMPLES::

                    sage: from pet_salon.immersion import Embeddings
                    sage: from pet_salon import PolytopeUnions, rectangle
                    sage: U = PolytopeUnions(2, QQ, nonoverlapping=False)
                    sage: union = U({0: rectangle(QQ,0,1,0,1)})
                    sage: E = Embeddings(union)
                    sage: E
                    Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: attempted_domain = U({1:rectangle(QQ,   0,1/2, 0, 1/2),
                    ....:                         2:rectangle(QQ, 1/2,  1, 0, 1/2)})
                    sage: attempted_domain
                    Disjoint union of 2 polyhedra in QQ^2
                    sage: su = E(attempted_domain,
                    ....:        { 1: 0, 2:0 }, # mapping to ambient label
                    ....:        { 0: attempted_domain})
                    sage: su
                    Embedding of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: su._test_nonoverlapping()
                    Traceback (most recent call last):
                    ...
                    AssertionError: The subunion associated to ambient label 0 is overlapping
                '''
                if length(self.subunions()) < infinity:
                    for ambient_label, subunion in self.subunions().items():
                        assert subunion.parent().is_nonoverlapping(), \
                            f'The subunion associated to ambient label {ambient_label} is overlapping'
                else:
                    for (ambient_label, subunion),_ in zip(self.subunions().items()), range(limit):
                        assert subunion.parent().is_nonoverlapping(), \
                            f'The subunion associated to ambient label {ambient_label} is overlapping'

    class Surjective(CategoryWithAxiom):
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self.rename(f'Category of surjective immersions into a polytope union')

        class SubcategoryMethods:

            def description(self):
                r'''Return a string describing the type of maps'''
                return 'Surjective immersion'

        class ParentMethods:

            def is_surjective(self):
                return True

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
                    sage: from pet_salon.immersion import SurjectiveEmbeddings
                    sage: U = PolytopeUnions(2, QQ)
                    sage: union = U(rectangle(QQ, 0, 1, 0, 1))
                    sage: union
                    Disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: P = SurjectiveEmbeddings(union)
                    sage: f = P(U({
                    ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
                    ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
                    ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
                    ....: }))
                    sage: f
                    Surjective embedding of disjoint union of 3 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: TestSuite(f).run()
                    Failure in _test_volume:
                    ...
                    The following tests failed: _test_volume
                '''
                def test_pair(ambient_label, subunion):
                    if subunion.is_finite():
                            assert subunion.volume() >= self.parent().ambient_union().polytope(ambient_label).volume(), \
                                f'The surjectivity axiom is violated: The volume of the subunion associated to the ambient label {ambient_label} is not at least as large as the ambient polytope\'s volume'
                if length(self.subunions()) < infinity:
                    for pair in self.subunions().items():
                        test_pair(*pair)
                else:
                    for pair,_ in zip(self.subunions().items(), range(limit)):
                        test_pair(*pair)

        class Injective(CategoryWithAxiom):
            r'''This is the category of surjective embeddings into a polytope union'''
            def __init__(self, *args, **options):
                CategoryWithAxiom.__init__(self, *args, **options)
                self.rename(f'Category of surjective embeddings into a polytope union')

            class SubcategoryMethods:

                def description(self):
                    r'''Return a string describing the type of maps'''
                    return 'Surjective embedding'

            class ParentMethods:

                def partitions(self):
                    return Partitions(self.ambient_union())

            class ElementMethods:

                def __invert__(self):
                    r'''Return the associated surjective embedding.'''
                    return self.parent().partitions()(self)

class Immersion(Element):
    def __init__(self, parent, domain, ambient_labels_mapping=None, subunions=None, name=None):
        self._domain = domain
        if not ambient_labels_mapping:
            assert 'Nonoverlapping' in parent.ambient_union().parent().category().axioms(), \
                'ambient_labels_mapping must be defined if the containing PolytopeUnion has overlaps'
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
                nonoverlapping = parent.is_injective()
                subunion_parent = domain.parent().with_different_axioms(finite=True, nonoverlapping=nonoverlapping)
                subunions[ambient_label] = domain.restrict(lst, parent=subunion_parent)
        self._domain = domain
        self._ambient_labels_mapping = ambient_labels_mapping
        self._subunions = subunions
        Element.__init__(self, parent)
        if name:
            self.rename(name)
        else:
            ambient_name = repr(parent.ambient_union())
#            axioms = parent.category().axioms()
#            if 'Injective' in axioms and 'Surjective' in axioms:
#                if domain.is_finite():
#                    number = len(domain.polytopes())
#                else:
#                    number = '∞ly many'
#                self.rename(f'Partition of {ambient_name[0].lower()}{ambient_name[1:]} into {number} subpolytopes')
#            else:
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
        if 'Nonoverlapping' in self.parent().ambient_union().parent().category().axioms():
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
        if 'Nonoverlapping' in self.parent().ambient_union().parent().category().axioms():
            return hash((self.parent(), self.domain()))
        else:
            if self.parent().ambient_union().is_finite():
                ambient_labels = frozenset((label,ambient_label) for label,ambient_label in self.ambient_labels().items())
                return hash((self.parent(), self.domain(), ambient_labels))
            else:
                return id(self)

    def _mul_(self, other):
        return self._act_on_(other, True)

    def _act_on_(self, other, self_on_left):
        r'''Implement the action of immersions on other immersions by composition.

        EXAMPLES::
            sage: from pet_salon import rectangle, PolytopeUnions
            sage: U = PolytopeUnions(2, QQ)
            sage: U
            Finite disjoint unions of nonoverlapping polyhedra in dimension 2 over Rational Field
            sage: u1 = U({1: rectangle(QQ, 0, 1, 0, 1)}, name='u1')
            sage: u2 = U({2: rectangle(QQ, 0, 2, 0, 2)}, name='u2')
            sage: u3 = U({3: rectangle(QQ, 0, 3, 0, 3)}, name='u3')
            sage: from pet_salon.immersion import Embeddings
            sage: i12 = Embeddings(u2)(u1) # embedding of u1 into u2
            sage: i23 = Embeddings(u3)(u2) # embedding of u2 into u3
            sage: i13 = Embeddings(u3)(u1) # embedding of u1 into u3
            sage: composition = i23*i12
            sage: composition
            Embedding of u1 into u3
            sage: composition == i13
            True
        '''
        if self_on_left:
            if other.parent and other.parent().category().is_subcategory(ImmersionsCategory()):
                if self.domain() != other.parent().ambient_union():
                    raise ValueError('To compose two immersions, the domain and codomain must be equal')
                injective = 'Injective' in self.parent().category().axioms() and 'Injective' in other.parent().category().axioms()
                surjective = 'Surjective' in self.parent().category().axioms() and 'Surjective' in other.parent().category().axioms()
                parent = self.parent().with_different_axioms(injective, surjective)
                return parent(other.domain(),
                       ambient_labels_mapping = mapping_composition(self.ambient_labels(), other.ambient_labels()),
                       # subunions = # We leave it to the constructor to work out the subunions.
                )
            PAMs = self.parent().piecewise_affine_maps()
            if PAMs.has_coerce_map_from(other.parent()):
                return PAMs(self) * PAMs(other)
            #raise ValueError('This left action is not implemented')
        #raise ValueError('Right actions not defined yet')

class Immersions(UniqueRepresentation, Parent):
    r'''
    Collection (parent) of the collection of immersions (or a restricted class of immersions) into a fixed disjoint union of polytopes.

    We call the fixed disjoint union the "ambient union."

    EXAMPLES::

    Construct the trivial SurjectiveEmbedding:

        sage: from pet_salon.immersion import SurjectiveEmbeddings
        sage: from pet_salon import PolytopeUnions
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U.an_element()
        sage: union
        Disjoint union of 2 nonoverlapping polyhedra in QQ^2
        sage: S = SurjectiveEmbeddings(union)
        sage: p = S() # p is the trivial SurjectiveEmbedding
        sage: p
        Surjective embedding of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 2 nonoverlapping polyhedra in QQ^2
        sage: p.domain() == union
        True
        sage: p.ambient_labels()
        {0: 0, 1: 1}
        sage: pt = p.domain().point((0,0))
        sage: pt
        Point(0, (0, 0))
        sage: pt == p.preimage(pt)
        True
        sage: pt == p(pt)
        True
    '''
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
                start = 'Surjective embeddings into'
            else:
                start = 'Surjective immersions into'
        self._ambient_union = ambient_union
        Parent.__init__(self, category=cat)
        union_name = repr(ambient_union)
        self.rename(f'{start} {union_name[0].lower()}{union_name[1:]}')

    def with_different_axioms(self, injective=False, surjective=False):
        r'''Return a parent with the provided axioms.'''
        return Immersions(self.ambient_union(), injective=injective, surjective=surjective)

    def with_different_union(self, new_ambient_union):
        r'''Return the same parent but with a different ambient union.'''
        return Immersions(new_ambient_union, self.is_injective(), self.is_surjective())

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
        if 'Surjective' in self.category().axioms() and ambient_label_collection != self.ambient_union().labels():
            raise ValueError('The only restriction that is surjective is the trivial one')
        U = PolytopeUnions(self.dimension(), self.field(), finite=True, nonoverlapping=True)
        return self(self.ambient_union().restrict(ambient_label_collection),
                    identity_mapping(ambient_label_collection),
                    function_mapping(ambient_label_collection,
                                     lambda ambient_label:U({ambient_label: self.ambient_union().polytope(ambient_label)})))

    def _element_constructor_(self, *args, **kwds):
        #print(f'Called element_constructor with args={args}, len(args)={len(args)}, kwds={kwds}')
        if len(args)==0:
            # Construct the trivial immersion
            return self.restriction(self.ambient_union().labels())
        if len(args)==1:
            if args[0]==0:
                # Construct the trivial immersion
                return self.restriction(self.ambient_union().labels())
            if hasattr(args[0], 'parent') and callable(args[0].parent) and \
                hasattr(args[0].parent(), 'category') and callable(args[0].parent().category) and \
                args[0].parent().category().is_subcategory(PolytopeUnionsCategory()):
                # arg[0] is a PolytopeUnion
                assert self.field() == args[0].parent().field(), \
                    'Currently the subunion must have the same base field as the ambient_union.'
                return self.element_class(self, args[0], **kwds)
        if len(args) in [2,3]:
            return self.element_class(self, *args)
        raise NotImplementedError()

    def _an_element_(self):
        r'''
        TODO: Return an element representative of the parent class.
        '''
        return self()

def SurjectiveImmersions(ambient_union):
    r'''Construct the collection of surjective embedings into the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import SurjectiveImmersions
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1))
        sage: union
        Disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: P = SurjectiveImmersions(union)
        sage: P
        Surjective immersions into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(P).run()
        sage: V = PolytopeUnions(2, QQ, nonoverlapping=False)
        sage: f = P(V({
        ....:     1: rectangle(QQ,   0, 2/3,   0, 1),
        ....:     2: rectangle(QQ, 1/3,   1,   0, 1),
        ....: }))
        sage: f
        Surjective immersion of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(f).run()
    '''
    return Immersions(ambient_union, injective=False, surjective=True)

def Embeddings(ambient_union):
    r'''Construct the collection of embeddings into the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import Embeddings
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1))
        sage: union
        Disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: E = Embeddings(union)
        sage: E
        Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(E).run()
        sage: e = E(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....: }))
        sage: e
        Embedding of disjoint union of 3 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(e).run()
    '''
    return Immersions(ambient_union, injective=True, surjective=False)

def SurjectiveEmbeddings(ambient_union):
    r'''Construct the collection of surjective embedings into the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import SurjectiveEmbeddings
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1))
        sage: union
        Disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: P = SurjectiveEmbeddings(union)
        sage: P
        Surjective embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(P).run()
        sage: f = P(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....:     4: rectangle(QQ, 1/2,   1, 1/2,   1),
        ....: }))
        sage: f
        Surjective embedding of disjoint union of 4 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(f).run()
    '''
    return Immersions(ambient_union, injective=True, surjective=True)

class PartitionsCategory(Category):
    r"""
    The category of polyhedral decompositions of an ambient polyhedral union.

    EXAMPLES::

        sage: from pet_salon.immersion import PartitionsCategory
        sage: PartitionsCategory()
        Category of partitions of a polytope union
    """
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of partitions of a polytope union')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.immersion import PartitionsCategory
            sage: C = PartitionsCategory()
            sage: C.super_categories()
            [Category of sets]
        """
        return [Sets()]

    class ParentMethods:

        @abstract_method
        def ambient_union(self):
            r'''Return the ambient polyhedral union. This is also the codomain of partitions in the collection viewed as maps.'''
            pass

        def field(self):
            return self.ambient_union().parent().field()

        def dimension(self):
            return self.ambient_union().parent().dimension()

        @cached_method
        def surjective_embeddings(self):
            r'''Return the collection of surjective embeddings into the ambient union.'''
            return SurjectiveEmbeddings(self.ambient_union())

        @cached_method
        def piecewise_affine_maps(self):
            from .affine import PiecewiseAffineMaps
            return PiecewiseAffineMaps(self.dimension(), self.field())

    class ElementMethods:

        @abstract_method
        def surjective_embedding(self):
            r'''Return the associated surjective embedding.'''

        def domain(self):
            r''''''
            return self.parent().ambient_union()

        def codomain(self):
            r''''''
            return self.surjective_embedding().domain()

        def subunions(self):
            r'''
            Return a mapping sending an `ambient_label` to the restriction of the subunion to polytopes
            contained within the polytope with the provided `ambient_label`.
            '''
            return self.surjective_embedding().subunions()

        def ambient_labels(self):
            r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
            return self.surjective_embedding().ambient_labels()

        def __invert__(self):
            r'''Return the associated surjective embedding.'''
            return self.surjective_embedding()

        def _test_surjective_embedding(self, tester=None):
            try:
                TestSuite(self.surjective_embedding()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The associated surjective embedding failed a test: {e}')

        def images(self, point, limit=None):
            r'''Return a generator listing all representations of the given point in the ambient union as a point in a polytope of the parititon (codomain).

            The function simply calls `preimage` of the `surjective_embedding()` with the paramter `all` set to `True`. The `limit` parmeter is passed to this
            method and is only relevant in case a polytope is partitioned into infinitely many subpolytopes.
            '''
            return self.surjective_embedding().preimage(point, all=True, limit=limit)

class Partition(Element):
    def __init__(self, parent, surjective_embedding, name=None):
        self._surjective_embedding = parent.surjective_embeddings()(surjective_embedding)
        Element.__init__(self, parent)
        if name:
            name = str(name)
            self.rename(name)
            self._surjective_embedding.rename(f'Surjective embedding associated to {name[0]}{name[1:]}')
        else:
            ambient_name = repr(parent.ambient_union())
            axioms = parent.category().axioms()
            if self.codomain().is_finite():
                number = len(self.codomain().polytopes())
            else:
                number = '∞ly many'
            self.rename(f'Partition of {ambient_name[0].lower()}{ambient_name[1:]} into {number} subpolytopes')

    def surjective_embedding(self):
        r'''Return the associated surjective embedding.'''
        return self._surjective_embedding

    def __eq__(self, other):
        if self is other:
            return True
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        return self.surjective_embedding() == other.surjective_embedding()

    def __ne__(self, other):
        return not self.__eq__(other)

    @cached_method
    def __hash__(self):
        return hash((self.parent(), self.surjective_embedding()))

    def __call__(self, pt):
        return self.surjective_embedding().preimage(pt)

    def _mul_(self, other):
        return self._act_on_(other, True)

    def _act_on_(self, other, self_on_left):
        if self_on_left:
            if other.parent and other.parent().category().is_subcategory(PartitionsCategory()):
                if self.domain() == other.codomain():
                    return ~((~other)*(~self))
            PAMs = self.parent().piecewise_affine_maps()
            if PAMs.has_coerce_map_from(other.parent()):
                return PAMs(self) * PAMs(other)

class Partitions(UniqueRepresentation, Parent):
    r'''
    The collection of partitions of a polytope union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import Partitions
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1), name='union')
        sage: union
        union
        sage: P = Partitions(union)
        sage: P
        Partitions of union
        sage: TestSuite(P).run()
        sage: f = P(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....:     4: rectangle(QQ, 1/2,   1, 1/2,   1),
        ....: }))
        sage: f
        Partition of union into 4 subpolytopes
        sage: TestSuite(f).run()
        sage: f(union.point((1/2,1/3)))
        Point(1, (1/2, 1/3))
    '''
    Element = Partition

    def __init__(self, ambient_union):
        self._ambient_union = ambient_union
        Parent.__init__(self, category=PartitionsCategory())
        union_name = repr(ambient_union)
        self.rename(f'Partitions of {union_name[0].lower()}{union_name[1:]}')

    def ambient_union(self):
        return self._ambient_union

    def __eq__(self, other):
        if not hasattr(other, 'category') or not callable(other.category) or other.category() != self.category():
            return False
        return self.ambient_union() == other.ambient_union()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.category(), self.ambient_union()))

    def _element_constructor_(self, *args, **kwds):
        #print(f'Called element_constructor with args={args}')
        if len(args)==1:
            if hasattr(args[0], 'parent') and callable(args[0].parent) and \
                hasattr(args[0].parent(), 'category') and callable(args[0].parent().category):

                if args[0].parent() == self:
                    # Note: Ignoring possible name definition.
                    return args[0]
                if args[0].parent().category().is_subcategory(PartitionsCategory()):
                    return self.element_class(self, args[0].surjective_embedding(), **kwds)
                if args[0].parent().category().is_subcategory(ImmersionsCategory().Surjective().Injective()):
                    return self.element_class(self, args[0], **kwds)
        if len(args) in [1, 2, 3]:
            if 'name' in kwds:
                name = kwds.pop(name)
                surjective_embedding = self.surjective_embeddings()(*args, **kwds)
                return self.element_class(self, surjective_embedding, name=name)
            else:
                surjective_embedding = self.surjective_embeddings()(*args, **kwds)
                return self.element_class(self, surjective_embedding)
        raise NotImplementedError()

    def _an_element_(self):
        return self(self.surjective_embeddings().an_element())

