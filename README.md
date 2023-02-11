# Description

Wishbone/BSV transactors

## Quickstart

### Create an environment for BSC
```shell
source env.sh
```

### Simulate
```shell
bsc -sim -u ./test/Tb.bsv
bsc -sim -e mkTb
./bsim
```

### Create RTL
```shell
bsc -verilog -u ./test/Tb.bsv
```

## References
* [Bluespec Inc., "BSV Training, Eg09: Interfacing to AXI4 Stream", 2013-2016](https://github.com/B-Lang-org/Documentation/blob/db1cca24c31a03e2442e873b0ea5f044af190fed/Tutorials/BSV_Training/Example_Programs/Eg09_AXI4_Stream.pdf)
* [Dan Gisselquist, "Building Formal Assumptions to Describe Wishbone Behaviour", 2017](http://zipcpu.com/zipcpu/2017/11/07/wb-formal.html)
