#!/bin/bash

coqc Ident.v
../Extraction/Wrapper.byte -i Ident -t ident -o ident.ll

coqc Fact.v
../Extraction/Wrapper.byte -i Fact -t fact -o fact.ll

coqc Even.v
../Extraction/Wrapper.byte -i Even -t even -o even.ll
