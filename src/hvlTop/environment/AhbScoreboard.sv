`ifndef AHB_SCOREBOARD_INCLUDED_
`define AHB_SCOREBOARD_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: apb_scoreboard
// Used to compare the data sent/received by the master with the slave's data sent/received
//--------------------------------------------------------------------------------------------
class AhbScoreboard extends uvm_scoreboard;
  `uvm_component_utils(AhbScoreboard)

  //Variable: ahb_master_tx_h
  //Declaring handle for ahb_master_tx
  ahb_master_tx ahb_master_tx_h;

  //Variable: ahb_slave_tx_h
  //Declaring handle for ahb_slaver_tx
  ahb_slave_tx ahb_slave_tx_h;
  
  //Variable: ahb_master_analysis_fifo
  //Used to store the ahb_master_data
  uvm_tlm_analysis_fifo#(ahb_master_tx) ahb_master_analysis_fifo;

  //Variable: ahb_slave_analysis_fifo
  //Used to store the ahb_slave_data
  uvm_tlm_analysis_fifo#(ahb_slave_tx) ahb_slave_analysis_fifo[];

  //Variable: ahb_master_tx_count
  //To keep track of number of transactions for master 
  int ahb_master_tx_count = 0;

  //Variable: ahb_slave_tx_count
  //To keep track of number of transactions for slave 
  int ahb_slave_tx_count = 0;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "ApbScoreboard", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void check_phase (uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);

endclass : apb_scoreboard

//--------------------------------------------------------------------------------------------
// Construct: new
// Initialization of new memory
//
// Parameters:
//  name - AhbScoreboard
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbScoreboard::new(string name = "ahb_scoreboard",uvm_component parent = null);
  super.new(name, parent);
  ahb_master_analysis_fifo = new("ahb_master_analysis_fifo",this);
  ahb_slave_analysis_fifo = new[NO_OF_SLAVES];
  
  foreach(ahb_slave_analysis_fifo[i]) begin
    ahb_slave_analysis_fifo[i] = new($sformatf("ahb_slave_analysis_fifo[%0d]",i),this);
  end
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbScoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
endfunction : build_phase

//--------------------------------------------------------------------------------------------
`endif
