//
// Generated by Bluespec Compiler, version 2023.01 (build 52adafa)
//
// On Wed Feb  8 18:12:28 CET 2023
//
//
// Ports:
// Name                         I/O  size props
// CYC_O                          O     1 reg
// STB_O                          O     1 reg
// WE_O                           O     1 reg
// ADR_O                          O    32 reg
// SEL_O                          O     4 reg
// DAT_O                          O    32 reg
// RDY_server_request_put         O     1 reg
// server_response_get            O    32 reg
// RDY_server_response_get        O     1 reg
// CLK                            I     1 clock
// RST_N                          I     1 reset
// STALL_I                        I     1
// ACK_I                          I     1
// DAT_I                          I    32 reg
// server_request_put             I    69 reg
// EN_server_request_put          I     1
// EN_server_response_get         I     1
//
// No combinational paths from inputs to outputs
//
//

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

module mkWishboneMasterXactor_32_32(CLK,
				    RST_N,

				    STALL_I,
				    ACK_I,
				    DAT_I,

				    CYC_O,

				    STB_O,

				    WE_O,

				    ADR_O,

				    SEL_O,

				    DAT_O,

				    server_request_put,
				    EN_server_request_put,
				    RDY_server_request_put,

				    EN_server_response_get,
				    server_response_get,
				    RDY_server_response_get);
  input  CLK;
  input  RST_N;

  // action method wishbone_put
  input  STALL_I;
  input  ACK_I;
  input  [31 : 0] DAT_I;

  // value method wishbone_cyc
  output CYC_O;

  // value method wishbone_stb
  output STB_O;

  // value method wishbone_we
  output WE_O;

  // value method wishbone_adr
  output [31 : 0] ADR_O;

  // value method wishbone_sel
  output [3 : 0] SEL_O;

  // value method wishbone_dat
  output [31 : 0] DAT_O;

  // action method server_request_put
  input  [68 : 0] server_request_put;
  input  EN_server_request_put;
  output RDY_server_request_put;

  // actionvalue method server_response_get
  input  EN_server_response_get;
  output [31 : 0] server_response_get;
  output RDY_server_response_get;

  // signals for module outputs
  wire [31 : 0] ADR_O, DAT_O, server_response_get;
  wire [3 : 0] SEL_O;
  wire CYC_O, RDY_server_request_put, RDY_server_response_get, STB_O, WE_O;

  // ports of submodule m_io_req
  wire [68 : 0] m_io_req$D_IN, m_io_req$D_OUT;
  wire m_io_req$CLR,
       m_io_req$DEQ,
       m_io_req$EMPTY_N,
       m_io_req$ENQ,
       m_io_req$FULL_N;

  // ports of submodule m_io_rsp
  wire [31 : 0] m_io_rsp$D_IN, m_io_rsp$D_OUT;
  wire m_io_rsp$CLR,
       m_io_rsp$DEQ,
       m_io_rsp$EMPTY_N,
       m_io_rsp$ENQ,
       m_io_rsp$FULL_N;

  // value method wishbone_cyc
  assign CYC_O = m_io_req$EMPTY_N ;

  // value method wishbone_stb
  assign STB_O = m_io_req$EMPTY_N ;

  // value method wishbone_we
  assign WE_O = m_io_req$D_OUT[68] ;

  // value method wishbone_adr
  assign ADR_O = m_io_req$D_OUT[63:32] ;

  // value method wishbone_sel
  assign SEL_O = m_io_req$D_OUT[67:64] ;

  // value method wishbone_dat
  assign DAT_O = m_io_req$D_OUT[31:0] ;

  // action method server_request_put
  assign RDY_server_request_put = m_io_req$FULL_N ;

  // actionvalue method server_response_get
  assign server_response_get = m_io_rsp$D_OUT ;
  assign RDY_server_response_get = m_io_rsp$EMPTY_N ;

  // submodule m_io_req
  FIFO2 #(.width(32'd69), .guarded(1'd1)) m_io_req(.RST(RST_N),
						   .CLK(CLK),
						   .D_IN(m_io_req$D_IN),
						   .ENQ(m_io_req$ENQ),
						   .DEQ(m_io_req$DEQ),
						   .CLR(m_io_req$CLR),
						   .D_OUT(m_io_req$D_OUT),
						   .FULL_N(m_io_req$FULL_N),
						   .EMPTY_N(m_io_req$EMPTY_N));

  // submodule m_io_rsp
  FIFO2 #(.width(32'd32), .guarded(1'd1)) m_io_rsp(.RST(RST_N),
						   .CLK(CLK),
						   .D_IN(m_io_rsp$D_IN),
						   .ENQ(m_io_rsp$ENQ),
						   .DEQ(m_io_rsp$DEQ),
						   .CLR(m_io_rsp$CLR),
						   .D_OUT(m_io_rsp$D_OUT),
						   .FULL_N(m_io_rsp$FULL_N),
						   .EMPTY_N(m_io_rsp$EMPTY_N));

  // submodule m_io_req
  assign m_io_req$D_IN = server_request_put ;
  assign m_io_req$ENQ = EN_server_request_put ;
  assign m_io_req$DEQ = m_io_req$EMPTY_N && !STALL_I ;
  assign m_io_req$CLR = 1'b0 ;

  // submodule m_io_rsp
  assign m_io_rsp$D_IN = DAT_I ;
  assign m_io_rsp$ENQ = m_io_rsp$FULL_N && ACK_I ;
  assign m_io_rsp$DEQ = EN_server_response_get ;
  assign m_io_rsp$CLR = 1'b0 ;
endmodule  // mkWishboneMasterXactor_32_32

