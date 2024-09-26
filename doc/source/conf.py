from pet_salon.version import version
#from sage_docbuild.conf import html_theme, html_theme_options, pygments_style, pygments_dark_style, html_css_files, skip_TESTS_block, default_role

# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'pet_salon'
copyright = '2024, W. Patrick Hooper'
author = 'W. Patrick Hooper'

# The version info for the project you're documenting, acts as replacement for
# |version| and |release|, also used in various other places throughout the
# built documents.
release = version

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = [
    # We need to use SageMath's autodoc to render nested classes in categories
    # correctly. Otherwise they just render as "alias for" in the
    # documentation.
    "sage_docbuild.ext.sage_autodoc",
    "sphinx.ext.todo",
    "sphinx.ext.mathjax",
    "sphinx.ext.viewcode",
    "sphinx.ext.intersphinx",
]

# Extensions when rendering .ipynb/.md notebooks
myst_enable_extensions = [
    "dollarmath",
    "amsmath",
]

# The master toctree document.
master_doc = "index"

templates_path = ['_templates']
exclude_patterns = []

# Allow linking to external projects, e.g., SageMath
intersphinx_mapping = {"sage": ("https://doc.sagemath.org/html/en/reference", None)}

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

html_theme = 'sphinx_rtd_theme'
html_static_path = ['_static']
