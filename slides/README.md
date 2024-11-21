
# UU Slides template

This repository contains a template for LaTeX beamer slides, adapted
from the popular Metropolis theme. It tries to adhere to the UU
guidelines for colours and fonts.

## Usage

To simply build the slides using xelatex use:

> xelatex slides.tex

If you do not want to use xelatex, it should be fairly easy to revert
to more standard fonts.

Alternatively, the Makefile includes commands for building the .tex
from Markdown using pandoc (for an example, see slides.md).

# Overview

The repository consists of the following files and directories:

* Makefile -- commands for building the slides;
* slides.md -- Markdown sources;
* slides.tex -- example TeX file, generated from slides.md;
* slides.pdf -- example slide deck, generated from slides.tex;
* .slides.md.pandoc -- emacs configuration for Pandoc major mode;
* img/uulogo.png -- the UU logo used on the first slide;
* include/ -- the Metropolis theme and UU specific customizations.
