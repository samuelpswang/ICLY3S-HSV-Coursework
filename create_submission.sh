#!/usr/bin/sh

rm -rf submission
mkdir submission
cp ./dafny/FullerWang.dfy submission
cp ./isabelle/FullerWang.thy submission
zip FullerWang.zip ./yosys/multiplier.sby ./yosys/multiplier.sv
mv FullerWang.zip submission
