`ifndef AHBSLAVEMONITORPROXY_INCLUDED_
`define AHBSLAVEMONITORPROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveMonitorProxy
//  This is the HVL side AhbSlaveMonitorProxy
//  It gets the sampled data from the HDL slave monitor and converts them into transaction items
//--------------------------------------------------------------------------------------------
class AhbSlaveMonitorProxy extends uvm_monitor; 
  `uvm_component_utils(AhbSlaveMonitorProxy)
  
  // Variable: ahbSlaveMonitorBFM
  // Declaring handle for ahb monitor bfm
  virtual AhbSlaveMonitorBFM ahbSlaveMonitorBFM;
   
  // Variable: ahbSlaveAgentConfig
  // Declaring handle for AhbSlaveAgentConfig class 
  AhbSlaveAgentConfig ahbSlaveAgentConfig;
    
  // Variable: ahbSlaveAnalysisPort
  // Declaring analysis port for the monitor port
  uvm_analysis_port#(AhbSlaveTransaction) ahbSlaveAnalysisPort;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveMonitorProxy", uvm_component parent);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : AhbSlaveMonitorProxy

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name   - AhbSlaveMonitorProxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbSlaveMonitorProxy::new(string name = "AhbSlaveMonitorProxy",uvm_component parent);
  super.new(name, parent);
  ahbSlaveAnalysisPort = new("ahbSlaveAnalysisPort",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//  Creates the required ports, gets the required configuration from confif_db
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveMonitorProxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual AhbSlaveMonitorBFM)::get(this,"","AhbSlaveMonitorBFM", ahbSlaveMonitorBFM)) begin
    `uvm_fatal("FATAL MDP CANNOT GET AHBSLAVE MONITOR BFM","cannot get() ahbSlaveMonitorBFM");
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
//  Pointing handle of monitor proxy in HDL BFM to this proxy method in HVL part
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveMonitorProxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  ahbSlaveMonitorBFM.ahbSlaveMonitorProxy = this;
endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
//  This task calls the monitor logic written in the monitor BFM at HDL side
//  Receives data packet from slave monitor bfm and converts into the transaction objects
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task AhbSlaveMonitorProxy::run_phase(uvm_phase phase);
  AhbSlaveTransaction ahbSlavePacket;

  `uvm_info(get_type_name(), $sformatf("Inside the slave monitor proxy"), UVM_LOW);
  ahbSlavePacket = AhbSlaveTransaction::type_id::create("slave Packet");
  
  ahbSlaveMonitorBFM.waitForResetn();

  forever begin
    ahbTransferCharStruct structDataPacket;
    ahbTransferConfigStruct  structConfigPacket; 
    AhbSlaveTransaction  ahbSlaveClonePacket;
    
    AhbSlaveConfigConverter :: fromClass (ahbSlaveAgentConfig, structConfigPacket);
    ahbSlaveMonitorBFM.sampleData (structDataPacket, structConfigPacket);
    AhbSlaveSequenceItemConverter :: toClass (structDataPacket, ahbSlavePacket);

    `uvm_info(get_type_name(),$sformatf("Received packet from slave monitor BFM: , \n %s", ahbSlavePacket.sprint()),UVM_HIGH)

    //Clone and publish the cloned item to the subscribers
    $cast(ahbSlaveClonePacket, ahbSlavePacket.clone());
    `uvm_info(get_type_name(),$sformatf("Sending packet via analysis port: , \n %s", ahbSlaveClonePacket.sprint()),UVM_HIGH)
    ahbSlaveAnalysisPort.write(ahbSlaveClonePacket);
  end

endtask : run_phase

`endif
