# coq-compile ##########################################################

TODO overview, credits, license?

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

TODO

## Development environment #############################################

### coq-ext-lib ########################################################

TODO

### Using proof general+emacs ##########################################

If you use proof general+emacs, then you can run `make .dir-locals.el`
in the top level directory to produce a .dir-locals.el. This will 
configure your proof general settings for this directory so that you can 
edit files interactively.