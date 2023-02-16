# JasperGold run script

clear -all

# read design
analyze -v2k -y ../../lib/Verilog ../../verilog/mkWishboneSlaveXactor_32_32_8.v

# read constraints
analyze -sv12 fv_WishboneSlaveXactor.sv

#elaborate -top mkWishboneSlaveXactor_32_32_8
elaborate -top mkWishboneSlaveXactor_32_32_8 -parameter fv.F_MAX_OUTSTANDING 8

clock CLK
reset -expression (!RST_N)

check_assumptions
prove -all

report
