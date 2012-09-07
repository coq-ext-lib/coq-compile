#!/bin/bash

if [ -e coq-ext-lib ]
then
  echo "************************************************************"
  echo "** you seem to already have coq-ext-lib installed"
  echo "** going to update"
  echo "************************************************************"
  (cd coq-ext-lib; git up)
else
  echo "************************************************************"
  echo "** You don't have coq-ext-lib. I'm going to pull it."
  echo "** If you have it already, you can sym-link it."
  echo "************************************************************"
  git clone git://github.com/coq-ext-lib/coq-ext-lib.git
  (cd coq-ext-lib; make)
fi
