# ********************************************************************
#  This file is part of pet_salon.
#
#        Copyright (C)      2024 W. Patrick Hooper
#
#  pet_salon is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 2 of the License, or
#  (at your option) any later version.
#
#  pet_salon is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with pet_salon. If not, see <https://www.gnu.org/licenses/>.
# ********************************************************************

from collections.abc import Mapping

from sage.misc.misc_c import prod
from sage.rings.infinity import infinity
from sage.structure.unique_representation import UniqueRepresentation

def length(collection):
    r'''Return the length of a collection or infinity if it is an infinite collection.

    EXAMPLES::
        sage: from pet_salon.collection import length
        sage: length([1,2,3])
        3
        sage: from sage.rings.integer_ring import ZZ
        sage: length(ZZ)
        +Infinity
    '''
    try:
        return len(collection)
    except (TypeError, NotImplementedError): # raised when __len__ returns infinity
        return infinity

class Identity(UniqueRepresentation):
    def __init__(self):
        pass
    def __call__(self, *args, **kwds):
        if len(args)>0:
            return args[0]
    def __repr__(self):
        return f'Identity'


class ConstantFunction(UniqueRepresentation):
    def __init__(self, constant):
        self._c = constant
    def __call__(self, *args, **kwds):
        return self._c
    def __repr__(self):
        return f'The constant function with value {self._c}'

#class _IdentityMapping(Mapping):
#    def __init__(self, collection):
#        self._c = collection
#    def __getitem__(self, key):
#        if key in self._c:
#            return key
#        else:
#            raise KeyError
#    def __iter__(self):
#        return self._c.__iter__()
#    def __len__(self):
#        return self._c.__len__()
#    def __repr__(self):
#        return f'Identity mapping on {self._c}'
#    def __eq__(self, other):
#        if isinstance(other, _IdentityMapping):
#            return self._c == other._c
#        return False
#    def __hash__(self):
#        return hash(self._c)

def constant_mapping(collection, constant):
    return function_mapping(collection, ConstantFunction(constant))

def identity_mapping(collection):
    r'''Return the identity mapping `{x:x for x in collection}` even if `collection` is infinite.

    EXAMPLES::

        sage: from pet_salon.collection import length, identity_mapping
        sage: im = identity_mapping([1,3])
        sage: im
        {1: 1, 3: 3}
        sage: length(im)
        2
        sage: im[3]
        3
        sage: im[2]
        Traceback (most recent call last):
        ...
        KeyError: 2

        sage: from pet_salon.collection import length, identity_mapping
        sage: im2 = identity_mapping(ZZ)
        sage: im2
        Function mapping with domain Integer Ring and function Identity
        sage: length(im2)
        +Infinity
        sage: im2[3]
        3
        sage: im2[5/2]
        Traceback (most recent call last):
        ...
        KeyError
        sage: for x,_ in zip(im2.items(), range(5)):
        ....:     print(x)
        (0, 0)
        (1, 1)
        (-1, -1)
        (2, 2)
        (-2, -2)
    '''
    return function_mapping(collection, Identity())

class _FunctionMapping(Mapping):
    r'''This class handles the infinite case of `function_mapping`.'''
    def __init__(self, collection, function):
        self._c = collection
        self._f = function
    def __getitem__(self, key):
        if key in self._c:
            return self._f(key)
        else:
            raise KeyError
    def __iter__(self):
        return self._c.__iter__()
    def __len__(self):
        return self._c.__len__()
    def __repr__(self):
        return f'Function mapping with domain {self._c} and function {self._f}'
    def __eq__(self, other):
        if isinstance(other, _FunctionMapping):
            return self._c == other._c and self._f == other._f
        return False
    def __hash__(self):
        return hash((self._c, self._f))

def function_mapping(collection, function):
    r'''Return the mapping `{x:function(x) for x in collection}` even if the collection is infinite.

    EXAMPLES::

        sage: from pet_salon.collection import length, function_mapping
        sage: fm = function_mapping(QQ, lambda x: x^2)
        sage: length(fm)
        +Infinity
        sage: fm[-3]
        9
        sage: fm[I]
        Traceback (most recent call last):
        ...
        KeyError
        sage: for pair,_ in zip(fm.items(), range(5)):
        ....:     print(pair)
        ....:
        (0, 0)
        (1, 1)
        (-1, 1)
        (1/2, 1/4)
        (-1/2, 1/4)
    '''
    if length(collection) < infinity:
        return {x:function(x) for x in collection}
    else:
        return _FunctionMapping(collection, function)

def tuple_singleton(x):
    r'''
    Returns the tuple `(x,)`.

    This is used in some places as the `function` argument to `function_mapping`.
    '''
    return (x,)

class _PostcompositionMapping(Mapping):
    r'''This class handles the infinite case of `postcomposition_mapping`.'''
    def __init__(self, mapping, function):
        self._m = mapping
        self._f = function
    def __getitem__(self, key):
        return self._f(self._m[key])
    def __iter__(self):
        return self._m.__iter__()
    def __len__(self):
        return self._m.__len__()
    def __repr__(self):
        return f'Postcomposition mapping with domain {self._m} and function {self._f}'
    def __eq__(self, other):
        if isinstance(other, _PostcompositionMapping):
            return self._m == other._m and self._f == other._f
        return False
    def __hash__(self):
        return hash((self._m, self._f))

def postcomposition_mapping(mapping, function):
    if length(mapping) < infinity:
        return {x:function(y) for x,y in mapping.items()}
    else:
        return _PostcompositionMapping(mapping, function)

class _ProductMapping(Mapping):
    r'''This class handles the infinite case of `product_mapping`.

    We pass a collection of mappings. The first mapping in the collection will
    be used as the key set.
    '''
    def __init__(self, keys, mappings):
        self._k = keys
        self._ms = mappings
    def __getitem__(self, key):
        return prod([m[key] for m in self._k])
    def __iter__(self):
        return self._k.__iter__()
    def __len__(self):
        return self._k.__len__()
    def __repr__(self):
        return f'Product of mappings {self._ms}.'
    def __eq__(self, other):
        if isinstance(other, _ProductMapping):
            return self._k == other._k and self._ms == other._ms
        return False
    def __hash__(self):
        return hash((self._k, self._ms))

def product_mapping(keys, mappings):
    if length(keys) < infinity:
        return {x:prod([m[x] for m in mappings]) for x in keys}
    else:
        return _ProductMapping(keys, mappings)

def mapping_composition(second, first):
    r'''Return the composition of the mapping: `return[i] = second[first[i]]`.

    The point is to allow this to work for infinite mappings. But we defer this.
    '''
    try:
        # Attempt to multiply the mappings. This gives a way to handle things if we were working with labels indexed by a group or something.
        composition = second*first
        if isinstance(composition,Mapping):
            return composition
    except TypeError:
        pass
    if length(first) < infinity:
        return {i: second[first_i] for i,first_i in first.items()}
    raise NotImplemented('Not yet implemented for infinite mappings.')
