# ********************************************************************
#  This file is part of pet_salon.
#
#        Copyright (C) 2024 W. Patrick Hooper
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

from sage.misc.prandom import random
from sage.plot.colors import hue
from sage.plot.text import text

class RandomColorChooser:
    r'''Generates random colors with prechosen saturation and value.'''

    def __init__(self, s=1, v=1):
        r'''Construct a random color chooser with the provided saturation `s` and value `v`.'''
        self._s = s
        self._v = v

    def change_parameters(self, s, v):
        r'''Change the saturation to `s` and the value to `v`.'''
        self._s = s
        self._v = v

    def get(self):
        r'''Generate a random color.'''
        return hue(random(), self._s, self._v)

label_random_color_chooser = RandomColorChooser(s=0.75, v=1)

_label_to_color = {}

def get_color(label):
    r'''Get a color associated to a label.'''
    try:
        return _label_to_color[label]
    except KeyError:
        color = label_random_color_chooser.get()
        _label_to_color[label] = color
        return color

def set_color(label, color):
    r'''Set the color associated to a label to the provided color.'''
    _label_to_color[label] = color

def plot_polytope_union(union, *args, fill=None, point = False, line = False, **kwds):
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
        plt2 = text(label, p.center(), color = "black")
        plt += plt2
    return plt

