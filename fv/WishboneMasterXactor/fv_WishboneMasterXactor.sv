/* Formal verification of Wishbone master
 *
 * Adapted from https://github.com/ZipCPU/zipcpu/blob/master/rtl/ex/fwb_master.v
 */

`default_nettype none

module fv_WishboneMasterXactor
  #(parameter F_MAX_OUTSTANDING = 1)
   (input wire  CLK,
    input wire  RST_N,

    // action method wishbone_put
    input wire  STALL_I,
    input wire  ACK_I,
    input wire  [31 : 0] DAT_I,

    // value method wishbone_cyc
    input wire CYC_O,

    // value method wishbone_stb
    input wire STB_O,

    // value method wishbone_we
    input wire WE_O,

    // value method wishbone_adr
    input wire [31 : 0] ADR_O,

    // value method wishbone_sel
    input wire [3 : 0] SEL_O,

    // value method wishbone_dat
    input wire [31 : 0] DAT_O,

    // action method server_request_put
    input wire  [68 : 0] server_request_put,
    input wire  EN_server_request_put,
    input wire RDY_server_request_put,

    // actionvalue method server_response_get
    input wire  EN_server_response_get,
    input wire [31 : 0] server_response_get,
    input wire RDY_server_response_get);

   bit signed [$clog2(F_MAX_OUTSTANDING+1):0] f_bsv_outstanding, f_outstanding;

   default clocking @(posedge CLK);
   endclocking;

   default disable iff (!RST_N);

   /********************************************************************************
    * BSV handshakes
    ********************************************************************************/

   property p_server_request_rdy_en;
      EN_server_request_put |-> RDY_server_request_put;
   endproperty
   a_server_request_rdy_en: assume property(p_server_request_rdy_en);

   property p_server_response_rdy_en;
      EN_server_response_get |-> RDY_server_response_get;
   endproperty
   a_server_response_rdy_en: assume property(p_server_response_rdy_en);

   // --------------------------------------------------------------------------

   // Count the number of outstanding BSV handshakes
   always @(posedge CLK)
     if (!RST_N)
       f_bsv_outstanding <= 0;
     else begin
        if (RDY_server_request_put && EN_server_request_put)   f_bsv_outstanding +=1;
        if (RDY_server_response_get && EN_server_response_get) f_bsv_outstanding +=1;
     end

   property p_bsv_overflow;
      f_outstanding <= F_MAX_OUTSTANDING;
   endproperty
   a_bsv_overflow: assume property(p_bsv_overflow);

   property p_bsv_underflow;
      f_outstanding >= 0;
   endproperty
   a_bsv_underflow: assume property(p_bsv_underflow);

   /********************************************************************************
    * Bus requests
    ********************************************************************************/

   // STB can only be true if CYC is also true
   property p_stb_cyc;
      STB_O |-> CYC_O;
   endproperty
   a_stb_cyc: assert property(p_stb_cyc);

   // --------------------------------------------------------------------------

   // If a request was both outstanding and stalled,
   // then nothing should change on the next clock regarding it.
   property p_stall_stable(x);
      CYC_O && STB_O && STALL_I |=> $stable(x);
   endproperty
   a_stall_stable_stb_o: assert property(p_stall_stable(STB_O));
   a_stall_stable_adr_o: assert property(p_stall_stable(ADR_O));
   a_stall_stable_sel_o: assert property(p_stall_stable(SEL_O));
   a_stall_stable_we_o: assert property(p_stall_stable(WE_O));

   property p_stall_stable_dat_o;
      CYC_O && STB_O && STALL_I && WE_O |=> $stable(DAT_O);
   endproperty
   a_stall_stable_dat_o: assert property(p_stall_stable_dat_o);

   // --------------------------------------------------------------------------

   // Write requests must also set one (or more) of SEL
   property p_req_wrt_sel;
      RDY_server_request_put && EN_server_request_put && server_request_put[68] |-> $countones(server_request_put[67:64] > 0);
   endproperty
   a_req_wrt_sel: assume property(p_req_wrt_sel);

   property p_wb_wrt_sel;
      STB_O && WE_O |-> $countones(SEL_O) > 0;
   endproperty
   a_wb_wrt_sel: assert property(p_wb_wrt_sel);

   /********************************************************************************
    * Bus responses
    ********************************************************************************/

   // If CYC was low on the last clock, then ACK should be low on this clock.
   property p_ncyc_nack;
      $past(!CYC_O) |-> !ACK_I;
   endproperty
   a_ncyc_nack: assume property(p_ncyc_nack);

   // --------------------------------------------------------------------------

   // Count the number of outstanding acknowledges
   always @(posedge CLK)
     if (!RST_N)
       f_outstanding <= 0;
     else begin
        if (STB_O && !STALL_I) f_outstanding += 1;
        if (ACK_I)             f_outstanding -= 1;
     end

   property p_overflow;
      f_outstanding <= F_MAX_OUTSTANDING;
   endproperty
   a_overflow: assert property(p_overflow);

   property p_underflow;
      f_outstanding >= 0;
   endproperty
   a_underflow: assert property(p_underflow);

   // --------------------------------------------------------------------------

   // every STB got exactly one ACK
   property p_stb_ack;
      $fell(CYC_O) |-> (f_outstanding == 0);
   endproperty
   a_stb_ack: assume property(p_stb_ack);
endmodule

bind mkWishboneMasterXactor_32_32_8 fv_WishboneMasterXactor fv(.*);
