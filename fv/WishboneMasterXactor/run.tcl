# JasperGold run script

clear -all

# read design
analyze -verilog -y ../../lib/Verilog ../../verilog/mkWishboneMasterXactor_32_32.v

# read constraints
analyze -sv12 fv_WishboneMasterXactor.sv

#elaborate -top mkWishboneMasterXactor_32_32
#elaborate -top mkWishboneMasterXactor_32_32 -parameter fv.F_MAX_STALL 3
#elaborate -top mkWishboneMasterXactor_32_32 -parameter fv.F_MAX_ACK_DELAY 5
#elaborate -top mkWishboneMasterXactor_32_32 -parameter fv.F_MAX_REQUESTS 7
elaborate -top mkWishboneMasterXactor_32_32 -parameter fv.F_MAX_ACK_DELAY 5 -parameter fv.F_MAX_REQUESTS 7
#elaborate -top mkWishboneMasterXactor_32_32 -parameter fv.F_MAX_STALL 3 -parameter fv.F_MAX_ACK_DELAY 5 -parameter fv.F_MAX_REQUESTS 7

clock CLK
reset -expression (!RST_N)

check_assumptions
prove -all
