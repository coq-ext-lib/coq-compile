#!/bin/bash

coqc Even.v
../Extraction/CpsKInterpTL.byte -n 1000 -i Even -t main -o even.res

