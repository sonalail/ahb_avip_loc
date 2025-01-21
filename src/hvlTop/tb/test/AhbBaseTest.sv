`ifndef AHBBASETEST_INCLUDED_
`define AHBBASETEST_INCLUDED_


//--------------------------------------------------------------------------------------------
// Class: AhbBaseTest
//  Base test has the testcase scenarios for the tesbench
//  Env and Config are created in AhbBaseTest
//  Sequences are created and started in the test
//--------------------------------------------------------------------------------------------
class AhbBaseTest extends uvm_test;
  `uvm_component_utils(AhbBaseTest)
  
  //Variable: env_h
  //Declaring a handle for env
  AhbEnvironment ahbEnvironment;

  //Variable: ahbEnvironmentConfig
  //Declaring a handle for env_cfg_h
  AhbEnvironmentConfig ahbEnvironmentConfig;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbBaseTest", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void setupAhbEnvironmentConfig();
  extern virtual function void setupAhbMasterAgentConfig();
  extern virtual function void setupAhbSlaveAgentConfig();
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : AhbBaseTest

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - AhbBaseTest
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbBaseTest::new(string name = "AhbBaseTest",uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//  Creates env and required configuarions
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbBaseTest::build_phase(uvm_phase phase);
  super.build_phase(phase);
  setupAhbEnvironmentConfig();
  ahbEnvironment = AhbEnvironment::type_id::create("ahbEnvironment",this);
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function : setup_AhbEnvironmentConfig
//  It calls the master agent config setup and slave agent config steup functions
//--------------------------------------------------------------------------------------------
function void AhbBaseTest::setupAhbEnvironmentConfig();
  ahbEnvironmentConfig = AhbEnvironmentConfig::type_id::create("ahbEnvironmentConfig");
  ahbEnvironmentConfig.no_of_slaves      = NO_OF_SLAVES;
  ahbEnvironmentConfig.has_scoreboard    = 1;
  ahbEnvironmentConfig.has_virtual_seqr  = 1;

  //Setting up the configuration for master agent
  setup_AhbMasterAgentConfig();

  //Setting the master agent configuration into config_db
   uvm_config_db#(AhbMasterAgentConfig)::set(this,"*master_agent*","AhbMasterAgentConfig",
                                               ahbEnvironmentConfig.ahbMasterAgentConfig);
 //Displaying the master agent configuration
  `uvm_info(get_type_name(),$sformatf("\nAHB_MASTER_AGENT_CONFIG\n%s",ahbEnvironmentConfig.ahbMasterAgentConfig.sprint()),UVM_LOW);

  setupAhbSlaveAgentConfig();

  uvm_config_db#(AhbEnvironmentConfig)::set(this,"*","AhbEnvironmentConfig",ahbEnvironmentConfig);
  `uvm_info(get_type_name(),$sformatf("\nAHB_ENV_CONFIG\n%s",ahbEnvironmentConfig.sprint()),UVM_LOW);

endfunction : setup_AhbEnvironmentConfig
//--------------------------------------------------------------------------------------------
// Function : setup_AhbMasterAgentConfig
//  Sets the configurations to the corresponding variables in ahb master agent config
//  Creates the master agent config
//  Sets ahb master agent config into configdb 
//--------------------------------------------------------------------------------------------
function void AhbBaseTest::setupAhbMasterAgentConfig();
  bit [63:0]local_min_address;
  bit [63:0]local_max_address;
  
  ahbEnvironmentConfig.ahbMasterAgentConfig = AhbMasterAgentConfig::type_id::create("AhbMasterAgentConfig");
  
  if(MASTER_AGENT_ACTIVE === 1) begin
    ahbEnvironmentConfig.ahbMasterAgentConfig.is_active = uvm_active_passive_enum'(UVM_ACTIVE);
  end
  else begin
    ahbEnvironmentConfig.ahbMasterAgentConfig.is_active = uvm_active_passive_enum'(UVM_PASSIVE);
  end
  ahbEnvironmentConfig.ahbMasterAgentConfig.no_of_slaves = NO_OF_SLAVES;
  ahbEnvironmentConfig.ahbMasterAgentConfig.has_coverage = 1;

  for(int i =0; i<NO_OF_SLAVES; i++) begin
    if(i == 0) begin  
      ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range(i,0);
      local_min_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range_array[i];
      
      ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range(i,2**(SLAVE_MEMORY_SIZE)-1 );
      local_max_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range_array[i];
    end
    else begin
      ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range(i,local_max_address + SLAVE_MEMORY_GAP);
      local_min_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range_array[i];
      
      ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range(i,local_max_address+2**(SLAVE_MEMORY_SIZE)-1 + SLAVE_MEMORY_GAP);
      local_max_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range_array[i];
    end
  end
endfunction : setup_AhbMasterAgentConfig
//--------------------------------------------------------------------------------------------
// Function : setup_AhbSlaveAgentConfig
//  It calls the master agent config setup and slave agent config steup functions
//--------------------------------------------------------------------------------------------
    
function void AhbBaseTest::setup_AhbSlaveAgentConfig();
  ahbEnvironmentConfig.ahb_slave_agent_cfg_h = new[ahbEnvironmentConfig.no_of_slaves];
  foreach(ahbEnvironmentConfig.ahbSlaveAgentConfig[i]) begin
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i] = AhbSlaveAgentConfig::type_id::create($sformatf("AhbSlaveAgentConfig[%0d]",i));
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i].slave_id       = i;
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i].slave_selected = 0;
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i].min_address    = ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range_array[i];
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i].max_address    = ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range_array[i];
    if(SLAVE_AGENT_ACTIVE === 1) begin
      ahbEnvironmentConfig.ahbSlaveAgentConfig[i].is_active = uvm_active_passive_enum'(UVM_ACTIVE);
    end
    else begin
      ahbEnvironmentConfig.ahbSlaveAgentConfig[i].is_active = uvm_active_passive_enum'(UVM_PASSIVE);
    end
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i].has_coverage = 1; 
    uvm_config_db #(AhbSlaveAgentConfig)::set(this,$sformatf("*env*"),$sformatf("AhbSlaveAgentConfig[%0d]",i),
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i]);
    `uvm_info(get_type_name(),$sformatf("\nAHB_SLAVE_CONFIG[%0d]\n%s",i,ahbEnvironmentConfig.ahbSlaveAgentConfig[i].sprint()),UVM_LOW);
  end

endfunction : setup_AhbSlaveAgentConfig

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
//  Used to print topology
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbBaseTest::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  uvm_top.print_topology();
endfunction  : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
//  Used to give 100ns delay to complete the run_phase.
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task AhbBaseTest::run_phase(uvm_phase phase);
  `uvm_info(get_type_name(),$sformatf("Inside run phase of test"),UVM_LOW);
  phase.raise_objection(this);
  super.run_phase(phase);
  #100;
  phase.drop_objection(this);

endtask : run_phase

`endif

