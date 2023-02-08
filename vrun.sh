#!/bin/zsh
set -e

bsc -vsim verilator -u ./test/Tb.bsv
bsc -vsim verilator -o vsim -e mkTb
./vsim $@
