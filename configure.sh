#!/bin/sh
# From https://github.com/Matafou/LibHyps/blob/master/configure.sh

FILES=`find . -name "*.v" -exec echo {} \;`
echo "-R NS NS" > _CoqProject
echo "" >> _CoqProject
for i in `find NS -name "*.v"| grep -v NSNaming2 | grep -v NSExamples | grep -v NSDemo | grep -v NSTest | grep -v NSRegression`; do
  echo $i >> _CoqProject
done
coq_makefile -f _CoqProject -o Makefile
