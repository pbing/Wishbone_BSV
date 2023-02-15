//
// Generated by Bluespec Compiler, version 2023.01 (build 52adafa)
//
// On Wed Feb 15 15:51:00 GMT 2023
//
//
// Ports:
// Name                         I/O  size props
// CLK                            I     1 clock
// RST_N                          I     1 reset
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

module mkTb(CLK,
	    RST_N);
  input  CLK;
  input  RST_N;

  // register m_dat
  reg [31 : 0] m_dat;
  wire [31 : 0] m_dat$D_IN;
  wire m_dat$EN;

  // register s_dat
  reg [31 : 0] s_dat;
  wire [31 : 0] s_dat$D_IN;
  wire s_dat$EN;

  // ports of submodule master
  wire [68 : 0] master$server_request_put;
  wire [31 : 0] master$ADR_O,
		master$DAT_I,
		master$DAT_O,
		master$server_response_get;
  wire [3 : 0] master$SEL_O;
  wire master$ACK_I,
       master$CYC_O,
       master$EN_server_request_put,
       master$EN_server_response_get,
       master$RDY_server_request_put,
       master$RDY_server_response_get,
       master$STALL_I,
       master$STB_O,
       master$WE_O;

  // ports of submodule slave
  wire [68 : 0] slave$client_request_get;
  wire [31 : 0] slave$ADR_I,
		slave$DAT_I,
		slave$DAT_O,
		slave$client_response_put;
  wire [3 : 0] slave$SEL_I;
  wire slave$ACK_O,
       slave$CYC_I,
       slave$EN_client_request_get,
       slave$EN_client_response_put,
       slave$RDY_client_request_get,
       slave$RDY_client_response_put,
       slave$STALL_O,
       slave$STB_I,
       slave$WE_I;

  // rule scheduling signals
  wire WILL_FIRE_RL_rl_master_request;

  // declarations used by system tasks
  // synopsys translate_off
  reg [63 : 0] v__h535;
  reg [63 : 0] v__h596;
  reg [63 : 0] v__h693;
  reg [63 : 0] v__h740;
  // synopsys translate_on

  // submodule master
  mkWishboneMasterXactor_32_32_8 master(.CLK(CLK),
					.RST_N(RST_N),
					.ACK_I(master$ACK_I),
					.DAT_I(master$DAT_I),
					.STALL_I(master$STALL_I),
					.server_request_put(master$server_request_put),
					.EN_server_request_put(master$EN_server_request_put),
					.EN_server_response_get(master$EN_server_response_get),
					.CYC_O(master$CYC_O),
					.STB_O(master$STB_O),
					.WE_O(master$WE_O),
					.ADR_O(master$ADR_O),
					.SEL_O(master$SEL_O),
					.DAT_O(master$DAT_O),
					.RDY_server_request_put(master$RDY_server_request_put),
					.server_response_get(master$server_response_get),
					.RDY_server_response_get(master$RDY_server_response_get));

  // submodule slave
  mkWishboneSlaveXactor_32_32_8 slave(.CLK(CLK),
				      .RST_N(RST_N),
				      .ADR_I(slave$ADR_I),
				      .CYC_I(slave$CYC_I),
				      .DAT_I(slave$DAT_I),
				      .SEL_I(slave$SEL_I),
				      .STB_I(slave$STB_I),
				      .WE_I(slave$WE_I),
				      .client_response_put(slave$client_response_put),
				      .EN_client_request_get(slave$EN_client_request_get),
				      .EN_client_response_put(slave$EN_client_response_put),
				      .STALL_O(slave$STALL_O),
				      .ACK_O(slave$ACK_O),
				      .DAT_O(slave$DAT_O),
				      .client_request_get(slave$client_request_get),
				      .RDY_client_request_get(slave$RDY_client_request_get),
				      .RDY_client_response_put(slave$RDY_client_response_put));

  // rule RL_rl_master_request
  assign WILL_FIRE_RL_rl_master_request =
	     master$RDY_server_request_put && m_dat <= 32'h10000008 ;

  // register m_dat
  assign m_dat$D_IN = m_dat + 32'd1 ;
  assign m_dat$EN = WILL_FIRE_RL_rl_master_request ;

  // register s_dat
  assign s_dat$D_IN = s_dat + 32'd1 ;
  assign s_dat$EN = slave$RDY_client_response_put ;

  // submodule master
  assign master$ACK_I = slave$ACK_O ;
  assign master$DAT_I = slave$DAT_O ;
  assign master$STALL_I = slave$STALL_O ;
  assign master$server_request_put = { 37'h0FAAAAAAAA, m_dat } ;
  assign master$EN_server_request_put = WILL_FIRE_RL_rl_master_request ;
  assign master$EN_server_response_get = master$RDY_server_response_get ;

  // submodule slave
  assign slave$ADR_I = master$ADR_O ;
  assign slave$CYC_I = master$CYC_O ;
  assign slave$DAT_I = master$DAT_O ;
  assign slave$SEL_I = master$SEL_O ;
  assign slave$STB_I = master$STB_O ;
  assign slave$WE_I = master$WE_O ;
  assign slave$client_response_put = s_dat ;
  assign slave$EN_client_request_get = slave$RDY_client_request_get ;
  assign slave$EN_client_response_put = slave$RDY_client_response_put ;

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        m_dat <= `BSV_ASSIGNMENT_DELAY 32'h10000001;
	s_dat <= `BSV_ASSIGNMENT_DELAY 32'h20000001;
      end
    else
      begin
        if (m_dat$EN) m_dat <= `BSV_ASSIGNMENT_DELAY m_dat$D_IN;
	if (s_dat$EN) s_dat <= `BSV_ASSIGNMENT_DELAY s_dat$D_IN;
      end
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    m_dat = 32'hAAAAAAAA;
    s_dat = 32'hAAAAAAAA;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on

  // handling of system tasks

  // synopsys translate_off
  always@(negedge CLK)
  begin
    #0;
    if (RST_N != `BSV_RESET_VALUE)
      if (WILL_FIRE_RL_rl_master_request)
	begin
	  v__h535 = $time;
	  #0;
	end
    if (RST_N != `BSV_RESET_VALUE)
      if (WILL_FIRE_RL_rl_master_request)
	$display("%t master request %h", v__h535, m_dat);
    if (RST_N != `BSV_RESET_VALUE)
      if (slave$RDY_client_request_get)
	begin
	  v__h596 = $time;
	  #0;
	end
    if (RST_N != `BSV_RESET_VALUE)
      if (slave$RDY_client_request_get)
	$display("%t     slave request %h",
		 v__h596,
		 slave$client_request_get[31:0]);
    if (RST_N != `BSV_RESET_VALUE)
      if (slave$RDY_client_response_put)
	begin
	  v__h693 = $time;
	  #0;
	end
    if (RST_N != `BSV_RESET_VALUE)
      if (slave$RDY_client_response_put)
	$display("%t         slave response %h", v__h693, s_dat);
    if (RST_N != `BSV_RESET_VALUE)
      if (master$RDY_server_response_get)
	begin
	  v__h740 = $time;
	  #0;
	end
    if (RST_N != `BSV_RESET_VALUE)
      if (master$RDY_server_response_get)
	$display("%t             master response %h",
		 v__h740,
		 master$server_response_get);
  end
  // synopsys translate_on
endmodule  // mkTb

