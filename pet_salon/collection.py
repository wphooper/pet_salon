# ********************************************************************
#  This file is part of pet-salon.
#
#        Copyright (C)      2024 W. Patrick Hooper
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

from sage.rings.infinity import infinity

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

class _IdentityMapping(Mapping):
    def __init__(self, collection):
        self._c = collection
    def __getitem__(self, key):
        if key in self._c:
            return key
        else:
            raise KeyError
    def __iter__(self):
        return self._c.__iter__()
    def __len__(self):
        return self._c.__len__()
    def __repr__(self):
        return f'Identity mapping on {self._c}'
    def __eq__(self, other):
        if isinstance(other, _IdentityMapping):
            return self._c == other._c
        return False
    def __hash__(self):
        return hash(self._c)

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
        Identity mapping on Integer Ring
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
    if length(collection) < infinity:
        return {x:x for x in collection}
    else:
        return _IdentityMapping(collection)

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
