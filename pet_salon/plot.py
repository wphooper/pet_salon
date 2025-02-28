# ********************************************************************
#  This file is part of pet_salon.
#
#        Copyright (C) 2024-2025 W. Patrick Hooper
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

'''
This module provides functionality for choosing colors for labels in plots.

A `ColorChooser` is a function or class that takes as input a label and returns a color. 
Color choosers are allowed to fail, instead raising a `ValueError` or `TypeError`.

This module maintains a list of color choosers in the module variable `COLOR_CHOOSERS`. The 
`get_color` method simply goes through the color choosers in `COLOR_CHOOSERS` in order
and returns the color returned by the first successful application of a color choser to this
label.

To explicitly select a color for a label, use the `set_color` method, which makes use of the
`DECLARE_COLOR_CHOOSER` instance of the `DeclareColorChooser` class.

Classes:
    - DeclareColorChooser: Allows explicit color assignment for each label.
    - RotationIntegerColorChooser: Generates colors for integer labels using a rotation and hue.
    - RandomColorChooser: Generates random colors with predefined saturation and value.

EXAMPLES::

    sage: from pet_salon.plot import COLOR_CHOOSERS
    sage: COLOR_CHOOSERS
    [DeclareColorChooser,
    RotationIntegerColorChooser(s=0.75, v=1, r=0.6180339887498949),
    RandomColorChooser(s=0.75, v=1)]

    sage: from pet_salon.plot import get_color, set_color
    sage: get_color(0)
    (1.0, 0.25, 0.25)
    sage: set_color('g', 'green')
    sage: get_color('g')
    'green'

    sage: from pet_salon.plot import ROTATION_INTEGER_COLOR_CHOOSER
    sage: from sage.misc.functional import sqrt
    sage: # Use colors as bright as possible with a rotation by sqrt(2)-1:
    sage: ROTATION_INTEGER_COLOR_CHOOSER.change_parameters(s=1, v=1, r=sqrt(2)-1)
    sage: get_color(0)
    (1.0, 0.0, 0.0)
'''

from collections.abc import Mapping

from sage.functions.other import floor
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.prandom import random
from sage.plot.colors import hue
from sage.plot.text import text
from sage.rings.real_double import RDF
from sage.rings.integer_ring import ZZ
from sage.symbolic.constants import golden_ratio

class ColorChooser:
    '''Abstract class to choose a color for a provided label.'''
    
    @abstract_method
    def __call__(self, label):
        '''Return a choice of a color for the provided label.
        
        If there is no way to choose a color, a `TypeError` or `ValueError` should be raised.'''
        pass

class DeclareColorChooser(ColorChooser):
    r'''This chooser lets the programmer explicitly choose a color for each label.'''
    def __init__(self):
        self._label_to_color = dict()

    def set(self, label, color):
        self._label_to_color[label] = color

    def __call__(self, label):
        try:
            return self._label_to_color[label]
        except KeyError:
            raise ValueError('Color for label not yet declared.')

    def __repr__(self):
        return 'DeclareColorChooser'

DECLARE_COLOR_CHOOSER = DeclareColorChooser()

class RandomColorChooser(ColorChooser):
    r'''Generates random colors with prechosen saturation and value.'''

    def __init__(self, s=1, v=1):
        r'''Construct a random color chooser with the provided saturation `s` and value `v`.'''
        self._s = s
        self._v = v

    @cached_method
    def __call__(self, label):
        r'''Generate a random color.'''
        return hue(random(), self._s, self._v)

    def __repr__(self):
        return f'RandomColorChooser(s={self._s}, v={self._v})'


class RotationIntegerColorChooser(ColorChooser):
    r'''Generates colors for integer labels using a rotation and hue.'''

    def __init__(self, s=1, v=1, r=None):
        r'''Construct a random color chooser with the provided saturation `s` and value `v`,
        and rotation given by `r` modulo one.'''
        self._s = s
        self._v = v
        if r is None:
            self._r = RDF(golden_ratio) - 1
        else:
            self._r = RDF(r)

    def change_parameters(self, s=1, v=1, r=None):
        r'''Change the saturation to `s` and the value to `v`.'''
        self._s = s
        self._v = v
        if r is not None:
            self._r = RDF(r)

    def __call__(self, integer_label):
        r'''Generate a random color.'''
        x = ZZ(integer_label)*self._r
        return hue(x - floor(x), self._s, self._v)

    def __repr__(self):
        return f'RotationIntegerColorChooser(s={self._s}, v={self._v}, r={self._r})'

ROTATION_INTEGER_COLOR_CHOOSER = RotationIntegerColorChooser(s=0.75)

COLOR_CHOOSERS = [
    DECLARE_COLOR_CHOOSER,
    ROTATION_INTEGER_COLOR_CHOOSER,
    RandomColorChooser(s=0.75, v=1),
]

def get_color(label):
    r'''Get a color associated to a label.
    
    EXAMPLES::

        sage: from pet_salon.plot import get_color
        sage: get_color(0)
        (1.0, 0.0, 0.0)
    '''
    for color_chooser in COLOR_CHOOSERS:
        try:
            return color_chooser(label)
        except (ValueError, TypeError):
            pass
    raise ValueError('Unable to select a color from available color choosers.')

def set_color(label, color):
    r'''Set the color associated to a label to the provided color.
    
    EXAMPLES::

        sage: from pet_salon.plot import get_color, set_color
        sage: set_color('g', 'green')
        sage: get_color('g')
        'green'
    '''
    DECLARE_COLOR_CHOOSER.set(label, color)

def plot_polytope_union(union, *args, fill=None, point = False, line = False, labels=True, **kwds):
    r'''Plot the polytopes making up the union. The union must be 2- or 3-dimensional.

    The important argument is `fill` which specifies how colors are chosen for the polytopes in the union.
    By default (`fill = None`), we select colors randomly but consistently across runs using `get_color`.
    You can also set `fill` to a dictionary or a function that sends labels to colors. In this way different
    colors can be chosen for each polytope in the union.

    EXAMPLES::

    Two dimensional examples::

        sage: from pet_salon import PolytopeUnions
        sage: from pet_salon.plot import plot_polytope_union
        sage: union = PolytopeUnions(2, QQ).an_element()
        sage: # Random cached colors:
        sage: plot_polytope_union(union) # not tested
        sage: # Chosen colors:
        sage: plot_polytope_union(union, fill={0:'red', 1:'blue'}, axes=False) # not tested

    Three dimensional example::

        sage: from pet_salon import PolytopeUnions
        sage: union = PolytopeUnions(3, QQ).an_element()
        sage: plot_polytope_union(union) # not tested
    '''
    assert union.parent().dimension() in [2,3], 'This plot function only works in dimensions 2 and 3'
    if fill is None:
        fill_parameter = get_color
    else:
        fill_parameter = fill
    plt = None
    for label, p in union.polytopes().items():
        if isinstance(fill_parameter, Mapping):
            fill = fill_parameter[label]
        elif callable(fill_parameter):
            fill = fill_parameter(label)
        plt2 = p.plot(*args, point=point, line=line, fill=fill, **kwds)
        if plt:
            plt += plt2
        else:
            plt = plt2
        if labels:
            plt2 = text(label, p.center(), color = "black")
            plt += plt2
    return plt