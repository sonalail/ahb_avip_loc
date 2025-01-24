
`ifndef APBMASTERMONITORPROXY_INCLUDED_
`define APBMASTERMONITORPROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterMonitorProxy
//  This is the HVL side AhbMasterMonitorProxy
//  It gets the sampled data from the HDL master monitor and converts them into transaction items
//--------------------------------------------------------------------------------------------
class AhbMasterMonitorProxy extends uvm_monitor; 
  `uvm_component_utils(AhbMasterMonitorProxy)
  
  // Variable: ahbMasterMonitorBFM
  // Declaring handle for AhbMasterMonitorBFM
  virtual AhbMasterMonitorBFM ahbMasterMonitorBFM;
   
  // Variable: ahbmasterAgentConfig
  // Declaring handle for AhbMasterAgentConfig class 
  AhbMasterAgentConfig ahbMasterAgentConfig;
    
  // Variable: ahbMasterAnalysisPort
  // Declaring analysis port for the monitor port
  uvm_analysis_port#(AhbMasterTransaction) ahbMasterAnalysisPort;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterMonitorProxy", uvm_component parent);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : AhbMasterMonitorProxy

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name   - AhbMasterMonitorProxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbMasterMonitorProxy::new(string name = "AhbMasterMonitorProxy",uvm_component parent);
  super.new(name, parent);
  ahbMasterAnalysisPort = new("ahbMasterAnalysisPort",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//  Creates the required ports, gets the required configuration from confif_db
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterMonitorProxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual AhbMasterMonitorBFM)::get(this,"","AhbMasterMonitorBFM", ahbMasterMonitorBFM)) begin
    `uvm_fatal("FATAL_MDP_CANNOT_GET_AHB_MASTER_MONITOR_BFM","cannot get() ahbMasterMonitorBFM");
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
//  Pointing handle of monitor proxy in HDL BFM to this proxy method in HVL part
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterMonitorProxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
ahbMasterMonitorBFM.ahbMasterMonitorProxy = this;
endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
//  This task calls the monitor logic written in the monitor BFM at HDL side
//  Receives data packet from slave monitor bfm and converts into the transaction objects
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task AhbMasterMonitorProxy::run_phase(uvm_phase phase);
  AhbMasterTransaction ahbMasterPacket;

  `uvm_info(get_type_name(), $sformatf("Inside the master_monitor_proxy"), UVM_LOW);
  ahbMasterPacket = AhbMasterTransaction::type_id::create("ahbMasterPacket");
  
  ahbMasterMonitorBFM.waitForResetn();

//  forever begin
    ahbTransferCharStruct structDataPacket;
    ahbTransferConfigStruct  structConfigPacket; 
    AhbMasterTransaction  ahbMasterClonePacket;
    
    AhbMasterConfigConverter :: fromClass(ahbMasterAgentConfig,  structConfigPacket);
    ahbMasterMonitorBFM.sampleData (structDataPacket,  structConfigPacket);
    AhbMasterSequenceItemConverter :: toClass(structDataPacket, ahbMasterPacket);

    `uvm_info(get_type_name(),$sformatf("Received packet from master monitor bfm: , \n %s", ahbMasterPacket.sprint()),UVM_HIGH)

    //Clone and publish the cloned item to the subscribers
    $cast(ahbMasterClonePacket, ahbMasterPacket.clone());
    `uvm_info(get_type_name(),$sformatf("Sending packet via analysis_port: , \n %s", ahbMasterClonePacket.sprint()),UVM_HIGH)
    ahbMasterAnalysisPort.write(ahbMasterClonePacket);
//  end

endtask : run_phase

`endif
