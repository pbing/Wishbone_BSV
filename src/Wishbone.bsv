package Wishbone;

export WishboneMaster_IFC(..), WishboneSlave_IFC(..),
WishboneMasterXactor_IFC(..), WishboneSlaveXactor_IFC(..),
mkWishboneMasterXactor, mkWishboneSlaveXactor;

import Connectable::*;
import ClientServer::*;
import FIFOF::*;
import Memory::*;

interface WishboneMaster_IFC#(numeric type aw, numeric type dw);
   (* prefix="" *)
   (* always_ready, always_enabled *) method Action put((* port="STALL_I" *) Bool stall,
                                                        (* port="ACK_I" *)   Bool ack,
                                                        (* port="DAT_I" *)   Bit#(dw) dat);

   (* always_ready, result="CYC_O" *) method Bool     cyc();
   (* always_ready, result="STB_O" *) method Bool     stb();
   (* always_ready, result="WE_O" *)  method Bool     we();
   (* always_ready, result="ADR_O" *) method Bit#(aw) adr();
   (* always_ready, result="SEL_O" *) method Bit#(TDiv#(dw, 8)) sel();
   (* always_ready, result="DAT_O" *) method Bit#(dw) dat();
endinterface

interface WishboneSlave_IFC#(numeric type aw, numeric type dw);
   (* prefix="" *)
   (* always_ready, always_enabled *) method Action put((* port="CYC_I" *) Bool cyc,
                                                        (* port="STB_I" *) Bool stb,
                                                        (* port="WE_I" *)  Bool we,
                                                        (* port="ADR_I" *) Bit#(aw) adr,
                                                        (* port="SEL_I" *) Bit#(TDiv#(dw, 8)) sel,
                                                        (* port="DAT_I" *) Bit#(dw) dat);

   (* always_ready, result="STALL_O" *) method Bool     stall();
   (* always_ready, result="ACK_O" *)   method Bool     ack();
   (* always_ready, result="DAT_O" *)   method Bit#(dw) dat();
endinterface

instance Connectable#(WishboneMaster_IFC#(aw, dw), WishboneSlave_IFC#(aw, dw));
   module mkConnection#(WishboneMaster_IFC#(aw, dw) wbm, WishboneSlave_IFC#(aw, dw) wbs) (Empty);
      (* fire_when_enabled, no_implicit_conditions *)
      rule rl_connect;
         wbm.put(wbs.stall, wbs.ack, wbs.dat);
         wbs.put(wbm.cyc, wbm.stb, wbm.we, wbm.adr, wbm.sel, wbm.dat);
      endrule
   endmodule
endinstance

interface WishboneMasterXactor_IFC#(numeric type aw, numeric type dw);
   (* prefix="" *)
   interface WishboneMaster_IFC#(aw, dw)                          wishbone;
   interface Server#(MemoryRequest#(aw, dw), MemoryResponse#(dw)) server;
endinterface

interface WishboneSlaveXactor_IFC#(numeric type aw, numeric type dw);
   (* prefix="" *)
   interface WishboneSlave_IFC#(aw, dw)                           wishbone;
   interface Client#(MemoryRequest#(aw, dw), MemoryResponse#(dw)) client;
endinterface

typedef enum {IDLE, ACTIVE} FSMState deriving (Bits, Eq);

module mkWishboneMasterXactor#(parameter Integer n) (WishboneMasterXactor_IFC#(aw, dw));
   FIFOF#(MemoryRequest#(aw, dw)) io_req    <- mkGFIFOF(False, True);
   FIFOF#(MemoryResponse#(dw))    io_rsp    <- mkGFIFOF(True, False);
   FIFOF#(Bit#(0))                hs_queue  <- mkUGSizedFIFOF(n);
   Reg#(FSMState)                 state     <- mkReg(IDLE);
   
   rule rl_fsm;
      case (state)
         IDLE:   if (io_req.notEmpty)    state <= ACTIVE;
         ACTIVE: if (!hs_queue.notEmpty) state <= IDLE;
      endcase
   endrule

   interface server = toGPServer(io_req, io_rsp);

   interface WishboneMaster_IFC wishbone;
      method Action put(Bool stall, Bool ack, Bit#(dw) dat);
         if (io_req.notEmpty && !stall) begin
            io_req.deq();
            if (hs_queue.notFull) hs_queue.enq(?);
         end

         if (ack) begin
            MemoryResponse#(dw) rsp = MemoryResponse {data: dat};
            if (io_rsp.notFull) io_rsp.enq(rsp);
            if (hs_queue.notEmpty) hs_queue.deq();
         end
      endmethod

      method Bool cyc();
         case (state)
            IDLE:   return io_req.notEmpty;
            ACTIVE: return io_req.notEmpty || hs_queue.notEmpty;
         endcase
      endmethod

      method Bool               stb() = io_req.notEmpty;
      method Bool               we()  = io_req.first.write;
      method Bit#(aw)           adr() = io_req.first.address;
      method Bit#(TDiv#(dw, 8)) sel() = io_req.first.byteen;
      method Bit#(dw)           dat() = io_req.first.data;
   endinterface
endmodule

module mkWishboneSlaveXactor#(parameter Integer n) (WishboneSlaveXactor_IFC#(aw, dw));
   FIFOF#(MemoryRequest#(aw, dw)) io_req    <- mkGFIFOF(True, False);
   FIFOF#(MemoryResponse#(dw))    io_rsp    <- mkGFIFOF(False, True);
   FIFOF#(Bit#(0))                req_queue <- mkUGSizedFIFOF(n);

   interface client = toGPClient(io_req, io_rsp);

   interface WishboneSlave_IFC wishbone;
      method Action put(Bool cyc, Bool stb, Bool we, Bit#(aw) adr, Bit#(TDiv#(dw, 8)) sel, Bit#(dw) dat);
         if (io_req.notFull && req_queue.notFull && cyc && stb) begin
            MemoryRequest#(aw, dw) req = MemoryRequest {write: we,
                                                        byteen: sel,
                                                        address: adr,
                                                        data: dat};
            io_req.enq(req);
            req_queue.enq(?);
         end
      
         if (!cyc)
            req_queue.clear();
         else if (io_rsp.notEmpty && req_queue.notEmpty) begin
            io_rsp.deq();
            req_queue.deq();
         end
      endmethod

      method Bool     stall() = !io_req.notFull;
      method Bool     ack()   = io_rsp.notEmpty && req_queue.notEmpty;
      method Bit#(dw) dat()   = io_rsp.first.data;
   endinterface
endmodule

endpackage
