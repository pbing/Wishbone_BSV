/* Formal verification of Wishbone slave
 *
 * Adapted from https://github.com/ZipCPU/zipcpu/blob/master/rtl/ex/fwb_slave.v
 */

`default_nettype none

module fv_WishboneSlaveXactor
  #(parameter F_MAX_OUTSTANDING = 1)
   (input wire  CLK,
    input wire  RST_N,

    // action method wishbone_put
    input wire  CYC_I,
    input wire  STB_I,
    input wire  WE_I,
    input wire  [31 : 0] ADR_I,
    input wire  [3 : 0] SEL_I,
    input wire  [31 : 0] DAT_I,

    // value method wishbone_stall
    input wire STALL_O,

    // value method wishbone_ack
    input wire ACK_O,

    // value method wishbone_dat
    input wire [31 : 0] DAT_O,

    // actionvalue method client_request_get
    input wire  EN_client_request_get,
    input wire [68 : 0] client_request_get,
    input wire RDY_client_request_get,

    // action method client_response_put
    input wire  [31 : 0] client_response_put,
    input wire  EN_client_response_put,
    input wire RDY_client_response_put);

   bit signed [$clog2(F_MAX_OUTSTANDING+1):0] f_bsv_outstanding, f_outstanding;

   default clocking @(posedge CLK);
   endclocking;

   default disable iff (!RST_N);

   /********************************************************************************
    * BSV handshakes
    ********************************************************************************/

   property p_client_request_rdy_en;
      EN_client_request_get |-> RDY_client_request_get;
   endproperty
   a_client_request_rdy_en: assume property(p_client_request_rdy_en);

   property p_client_response_rdy_en;
      EN_client_response_put |-> RDY_client_response_put;
   endproperty
   a_client_response_rdy_en: assume property(p_client_response_rdy_en);


   // --------------------------------------------------------------------------

   // Count the number of outstanding BSV handshakes
   always @(posedge CLK)
     if (!RST_N)
       f_bsv_outstanding <= 0;
     else begin
        if (RDY_client_request_get && EN_client_request_get)   f_bsv_outstanding +=1;
        if (RDY_client_response_put && EN_client_response_put) f_bsv_outstanding +=1;
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
      STB_I |-> CYC_I;
   endproperty
   a_stb_cyc: assume property(p_stb_cyc);

   // --------------------------------------------------------------------------

   // If a request was both outstanding and stalled,
   // then nothing should change on the next clock regarding it.
   property p_stall_stable(x);
      CYC_I && STB_I && STALL_O |=> $stable(x);
   endproperty
   a_stall_stable_stb_i: assume property(p_stall_stable(STB_I));
   a_stall_stable_adr_i: assume property(p_stall_stable(ADR_I));
   a_stall_stable_sel_i: assume property(p_stall_stable(SEL_I));
   a_stall_stable_we_i: assume property(p_stall_stable(WE_I));

   property p_stall_stable_dat_i;
      CYC_I && STB_I && STALL_O && WE_I |=> $stable(DAT_I);
   endproperty
   a_stall_stable_dat_i: assume property(p_stall_stable_dat_i);

   // --------------------------------------------------------------------------

   // Write requests must also set one (or more) of SEL
   property p_req_wrt_sel;
      RDY_client_request_get && client_request_get[68] |-> $countones(client_request_get[67:64] > 0);
   endproperty
   a_req_wrt_sel: assert property(p_req_wrt_sel);

   property p_wb_wrt_sel;
      STB_I && WE_I |-> $countones(SEL_I) > 0;
   endproperty
   a_wb_wrt_sel: assume property(p_wb_wrt_sel);

   /********************************************************************************
    * Bus responses
    ********************************************************************************/

   // If CYC was low on the last clock, then ACK should be low on this clock.
   property p_ncyc_nack;
      $past(!CYC_I) |-> !ACK_O;
   endproperty
   a_ncyc_nack: assert property(p_ncyc_nack);

   // --------------------------------------------------------------------------

   // Count the number of outstanding acknowledges
   always @(posedge CLK)
     if (!RST_N)
       f_outstanding <= 0;
     else begin
        if (STB_I && !STALL_O) f_outstanding += 1;
        if (ACK_O)             f_outstanding -= 1;
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
      $fell(CYC_I) |-> (f_outstanding == 0);
   endproperty
   a_stb_ack: assume property(p_stb_ack);
endmodule

bind mkWishboneSlaveXactor_32_32_8 fv_WishboneSlaveXactor fv(.*);
