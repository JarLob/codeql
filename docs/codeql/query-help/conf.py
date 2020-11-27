# -*- coding: utf-8 -*-
#
# CodeQL query help configuration file
#
# This file is execfile()d with the current directory set to its
# containing dir.
#
# Note that not all possible configuration values are present in this
# autogenerated file.
#
# All configuration values have a default; values that are commented out
# serve to show the default.

# For details of all possible config values, 
# see https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project-specific configuration -----------------------------------

# The master toctree document.
master_doc = 'index'

# General information about the project.
project = u'CodeQL query help'

# Add md parser to process query help markdown files 
extensions =['recommonmark']

source_suffix = {
    '.rst': 'restructuredtext',
    '.md': 'markdown',
}

# -- Project-specifc options for HTML output ----------------------------------------------

# Theme options are theme-specific and customize the look and feel of a theme
# further.  For a list of options available for each theme, see the
# documentation.
html_theme_options = {'font_size': '16px',
                      'body_text': '#333', 
                      'link': '#2F1695',
                      'link_hover': '#2F1695',
                      'show_powered_by': False,
                      'nosidebar':True,
                      'head_font_family': '-apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif, "Apple Color Emoji", "Segoe UI Emoji"',
                      }

highlight_language = "none"

# Add any paths that contain templates here, relative to this directory.
templates_path = ['../_templates']

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['../_static']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.

exclude_patterns = ['toc-*'] # ignore toc-<lang>.rst files as they are 'included' in index pages