# coq-compile ##########################################################

This is a compiler from Gallina (the logic language of the Coq proof
assistant) to LLVM. In addition to the core logical language, the
compiler also supports a limited number of extensions to perform input
and output in order to make programs more useful.

## Design Philosophy ###################################################

The compiler is written exclusively in Coq in a Haskell-like style
using coq-ext-lib, an augemented/alternative standard library that
utilizes first-class abstractions like type classes rather than
second-class abstractions like functors and modules.  See the
coq-ext-lib project (https://github.com/coq-ext-lib/coq-ext-lib) for
more information.

## Credits #############################################################

The compiler started as a course project in a graduate seminar on
functional language compilers taught by Greg Morrisett
(http://www.eecs.harvard.edu/~greg/). The course webpage is here
(http://www.eecs.harvard.edu/~greg/cs252rfa12/). The primary
contributers to the core compiler have been (in alphabetical order):

- Dan Huang (optimization & analysis)
- Gregory Malecha (core & optimization & analysis)
- Scott Moore (runtime)

# Getting Started ######################################################

## Prerequisites #######################################################

### Coq 8.4 ############################################################

coq-ext-lib requires Coq 8.4, which you can download from
http://coq.inria.fr/download.

Since it made some interface changes, you may also want the latest proof 
general:
   http://proofgeneral.inf.ed.ac.uk/devel.

### LLVM & Clang #######################################################

You need version 3.1 of LLVM and clang. If your package manager does not
have these packages available, you can download and build LLVM and clang
by following the instructions at http://llvm.org/docs/GettingStarted.html.
Be sure to replace `/trunk` with `/branches/release_31` in each `svn checkout` 
command.

### ocamlbuild #########################################################

ocamlbuild is used to extract the compiler. If your package manager does
not include ocamlbuild, it is available at (TODO).

## Building ############################################################

TODO

## Running #############################################################

TODO

# Contributing #########################################################

If you're interested in the compiler, we'd love for you to join the
project and learn something about compilers and something about Coq.

Check the issues page on GitHub and file a new issue for the feature(s)
you'd like (if one doesn't already exist). 

## Development environment #############################################

### coq-ext-lib ########################################################

TODO

### Using proof general+emacs ##########################################

If you use proof general+emacs, then you can run `make .dir-locals.el`
in the top level directory to produce a .dir-locals.el. This will 
configure your proof general settings for this directory so that you can 
edit files interactively.