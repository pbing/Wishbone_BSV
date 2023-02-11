/* Formal verification of Wishbone master
 *
 * Adapted from https://github.com/ZipCPU/zipcpu/blob/master/rtl/ex/fwb_master.v
 */

`default_nettype none

module fv_WishboneMasterXactor
  #(parameter F_MAX_STALL = 0,
    parameter F_MAX_ACK_DELAY = 0,
    parameter F_MAX_REQUESTS = 1)
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

   bit [$clog2(F_MAX_REQUESTS+1)-1:0] f_nreqs, f_nacks;

   default clocking @(posedge CLK);
   endclocking;

   default disable iff (!RST_N);

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

   // Within any series of STB/requests, the direction of the request
   // may not change.
   property p_stb_stable_we;
      $past(STB_O) && STB_O |-> $stable(WE_O);
   endproperty
   //FIXME a_stb_stable_we: assert property(p_stb_stable_we);

   // --------------------------------------------------------------------------

   // Within any given bus cycle, the direction may *only* change when
   // there are no further outstanding requests.
   //always @(posedge i_clk)
   //  if ((f_past_valid)&&(f_outstanding > 0))
   //    `SLAVE_ASSUME(i_wb_we == $past(i_wb_we));

   // --------------------------------------------------------------------------

   // Write requests must also set one (or more) of SEL
   property p_req_wrt_sel;
      server_request_put[68] |-> $countones(server_request_put[67:64] > 0);
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

   // Any time the CYC line drops, it is possible that there may be a
   // remaining (registered) ACK or ERR that hasn't yet been returned.
   // Restrict such out of band returns so that they are *only* returned
   // if there is an outstanding operation.
   //
   // Update: As per spec, WB-classic to WB-pipeline conversions require
   // that the ACK|ERR might come back on the same cycle that STB
   // is low, yet also be registered.  Hence, if STB & STALL are true on
   // one cycle, then CYC is dropped, ACK|ERR might still be true on the
   // cycle when CYC is dropped
   function [$clog2(F_MAX_REQUESTS+1)-1:0] f_outstanding();
      return f_nreqs - f_nacks;
   endfunction

   // Note that, unlike f_outstanding, f_nreqs and f_nacks are both
   // registered.  Hence, we can check here if a response is still
   // pending.  If not, no response should be returned.
   property p_max_requests;
      $fell(CYC_O) && (f_outstanding() == 0) |-> !ACK_I;
   endproperty
   a_max_requests: assume property(p_max_requests);

   // --------------------------------------------------------------------------

   // Assume the slave cannnot stall for more than F_MAX_STALL
   // counts.  We'll count this forward any time STB and STALL
   // are both true.
   generate
      if (F_MAX_STALL > 0) begin
         bit [$clog2(F_MAX_STALL+1)-1:0] f_stall_count;

         always @(posedge CLK or negedge RST_N)
           if (!RST_N)
             f_stall_count <= 0;
           else
             if (STB_O && STALL_I)
               f_stall_count += 1;
             else
               f_stall_count <= 0;

         property p_max_stall;
            CYC_O |-> (f_stall_count < F_MAX_STALL);
         endproperty
         a_max_stall: assume property(p_max_stall);
      end
   endgenerate

   // --------------------------------------------------------------------------

   // Assume the slave will respond within F_MAX_ACK_DELAY cycles,
   // counted either from the end of the last request, or from the
   // last ACK received
   generate
      if (F_MAX_ACK_DELAY > 0) begin
         bit[$clog2(F_MAX_ACK_DELAY+1)-1:0] f_ackwait_count;

         always @(posedge CLK or negedge RST_N)
           if (!RST_N)
             f_ackwait_count <= 0;
           else
             if (CYC_O && !STB_O && !ACK_I && (f_outstanding() > 0))
               f_ackwait_count += 1;
             else
               f_ackwait_count <= 0;

         property p_max_ack_delay;
            CYC_O && !STB_O && !ACK_I && (f_outstanding() > 0) |-> (f_ackwait_count < F_MAX_ACK_DELAY);
         endproperty
         a_max_ack_delay: assume property(p_max_ack_delay);
      end
   endgenerate

   // Count the number of requests that have been made
   always @(posedge CLK or negedge RST_N)
     if (!RST_N)
       f_nreqs <= 0;
     else
       if (!CYC_O)
         f_nreqs <= 0;
       else if (STB_O && !STALL_I)
         f_nreqs += 1;

   // Count the number of acknowledgements that have been received
   always @(posedge CLK or negedge RST_N)
     if (!RST_N)
       f_nacks <= 0;
     else
       if (!CYC_O)
         f_nacks <= 0;
       else if (ACK_I)
         f_nacks += 1;

   // --------------------------------------------------------------------------

   //property p_nreqs_1;
   //   CYC_O && STB_O |-> (f_nreqs < F_MAX_REQUESTS);
   //endproperty
   //a_nreqs_1: assert property(p_nreqs_1);

   property p_nreqs_2;
      CYC_O && !STB_O |-> (f_nreqs <= F_MAX_REQUESTS);
   endproperty
   a_nreqs_2: assert property(p_nreqs_2);

   property p_nreqs_nacks;
      CYC_O |-> (f_nacks <= f_nreqs);
   endproperty
   a_nregs_nacks: assume property(p_nreqs_nacks);

   // --------------------------------------------------------------------------

   // If nothing is outstanding, then there should be
   // no acknowledgements ... however, an acknowledgement
   // *can* come back on the same clock as the stb is
   // going out.
   property p_outstanding_1;
      CYC_O && (f_outstanding() == 0) |-> !ACK_I || (STB_O && !STALL_I);
   endproperty
   a_outstanding_1: assume property(p_outstanding_1);

   property p_outstanding_2;
      !CYC_O && (f_outstanding() == 0) |-> !ACK_I;
   endproperty
   a_outstanding_2: assume property(p_outstanding_2);

   // --------------------------------------------------------------------------

   // If we aren't waiting for anything, and we aren't issuing
   // any requests, then then our transaction is over and we
   // should be dropping the CYC line.
   property p_end_request;
      (f_outstanding() == 0) |-> STB_O || !CYC_O;
   endproperty
   // FIXME a_end_request: assert property(p_end_request);
   // Not all masters will abide by this restriction.  Some
   // masters may wish to implement read-modify-write bus
   // interactions.  These masters need to keep CYC high between
   // transactions, even though nothing is outstanding.  For
   // these busses, turn F_OPT_RMW_BUS_OPTION on.
   
   // --------------------------------------------------------------------------

   property p_xactions(n);
      //$rose(CYC_O) |=> (ACK_I[=n] within CYC_O[*n:$]) ##1 (!CYC_O and !ACK_I);
      $fell(CYC_O) |-> (f_nreqs == n && f_nacks == n);
   endproperty
   c_1_xaction: cover property(p_xactions(1));

   generate
      if (F_MAX_REQUESTS >= 2) c_2_xactions: cover property(p_xactions(2));
      if (F_MAX_REQUESTS >= 5) c_5_xactions: cover property(p_xactions(5));
   endgenerate
endmodule

bind mkWishboneMasterXactor_32_32 fv_WishboneMasterXactor fv(.*);
