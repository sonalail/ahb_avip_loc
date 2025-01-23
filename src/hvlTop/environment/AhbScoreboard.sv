`ifndef AHBSCOREBOARD_INCLUDED_
`define AHBSCOREBOARD_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbScoreboard
// Used to compare the data sent/received by the master with the slave's data sent/received
//--------------------------------------------------------------------------------------------
class AhbScoreboard extends uvm_scoreboard;
  `uvm_component_utils(AhbScoreboard)

  //Variable: ahbMasterTransaction
  //Declaring handle for AhbMasterTransaction
  AhbMasterTransaction ahbMasterTransaction;

  //Variable: ahbSlaveTransaction
  //Declaring handle for AhbSlaveTransaction
  AhbSlaveTransaction ahbSlaveTransaction;

  //Variable: ahb_master_analysis_fifo
  //Used to store the ahb_master_data
  uvm_tlm_analysis_fifo#(AhbMasterTransaction) ahbMasterAnalysisFifo[];

  //Variable: ahbSlaveAnalysisFifo
  //Used to store the ahb_slave_data
  uvm_tlm_analysis_fifo#(AhbSlaveTransaction) ahbSlaveAnalysisFifo[];

  //Variable: ahbMasterTransactionCount
  //To keep track of number of transactions for master
  int ahbMasterTransactionCount = 0;

  //Variable: ahbSlaveTransactionCount
  //To keep track of number of transactions for slave
  int ahbSlaveTransactionCount = 0;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbScoreboard", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void check_phase (uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);

endclass : AhbScoreboard

//--------------------------------------------------------------------------------------------
// Construct: new
// Initialization of new memory
//
// Parameters:
//  name - AhbScoreboard
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbScoreboard::new(string name = "AhbScoreboard",uvm_component parent = null);
  super.new(name, parent);
  ahbMasterAnalysisFifo = new[NO_OF_MASTERS];
  ahbSlaveAnalysisFifo = new[NO_OF_SLAVES];

  foreach(ahbMasterAnalysisFifo[i]) begin
    ahbMasterAnalysisFifo[i] = new($sformatf("ahbMasterAnalysisFifo[%0d]",i),this);
  end
  
  foreach(ahbSlaveAnalysisFifo[i]) begin
    ahbSlaveAnalysisFifo[i] = new($sformatf("ahbSlaveAnalysisFifo[%0d]",i),this);
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
// Task: run_phase
// Used to give delays and check the wdata and rdata are similar or not
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task AhbScoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  `uvm_info(get_type_name(),$sformatf("Entering the run phases of scoreboard"),UVM_HIGH)
  // forever begin
  //   ahbMasterAnalysisFifo.get(ahbMasterTransaction);
  //   ahbMasterAnalysisFifo.get(ahbSlaveTransaction);
  // end
endtask : run_phase

//--------------------------------------------------------------------------------------------
// Function: check_phase
//  Display the result of simulation
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbScoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
endfunction : check_phase

//--------------------------------------------------------------------------------------------
// Function: report_phase
//  Display the result of simulation
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbScoreboard::report_phase(uvm_phase phase);
  super.report_phase(phase);
endfunction : report_phase

//--------------------------------------------------------------------------------------------
`endif
