package Tb;

import ClientServer::*;
import Connectable::*;
import GetPut::*;
import Memory::*;
import Wishbone::*;


(* synthesize *)
module mkWishboneMasterXactor_32_32_8(WishboneMasterXactor_IFC#(32, 32));
   let m <- mkWishboneMasterXactor(8);
   return m;
endmodule

(* synthesize *)
module mkWishboneSlaveXactor_32_32_8(WishboneSlaveXactor_IFC#(32, 32));
   let m <- mkWishboneSlaveXactor(8);
   return m;
endmodule

(* synthesize *)
module mkTb(Empty);
   WishboneMasterXactor_IFC#(32, 32) master <- mkWishboneMasterXactor_32_32_8;
   WishboneSlaveXactor_IFC#(32, 32)  slave  <- mkWishboneSlaveXactor_32_32_8;
   Reg#(Bit#(32))                    m_dat <- mkReg('h10000001);
   Reg#(Bit#(32))                    s_dat <- mkReg('h20000001);
   Reg#(int)                         cycles <- mkReg(0);
   
   mkConnection(master.wishbone, slave.wishbone);
   
   rule rl_cycles;
      cycles <= cycles + 1;
      if (cycles == 30) $finish(0);
   endrule
   
   rule rl_master_request;
      MemoryRequest#(32, 32) req = MemoryRequest {write: ?,
                                                  byteen: '1,
                                                  address: ?,
                                                  data: m_dat};
      master.server.request.put(req);
      m_dat <= m_dat + 1;
      $display("%t master request %h", $time, req.data);
   endrule
   
   rule rl_slave (cycles % 5 == 0 || cycles % 7 == 0 || cycles % 11 == 0);
      let req <- slave.client.request.get();
      $display("%t     slave request %h", $time, req.data);

      MemoryResponse#(32) rsp = MemoryResponse {data: s_dat};
      slave.client.response.put(rsp);
      s_dat <= s_dat + 1;
      $display("%t         slave response %h", $time, rsp.data);
   endrule
      
   rule rl_master_response;
      let rsp <- master.server.response.get();
      $display("%t             master response %h", $time, rsp.data);
   endrule
   
endmodule

endpackage
