`ifndef AHB_BASE_TEST_INCLUDED_
`define AHB_BASE_TEST_INCLUDED_


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
  AhbEnvironment ahb_env_h;

  //Variable: ahb_env_cfg_h
  //Declaring a handle for env_cfg_h
  AhbEnvironmentConfig ahb_env_cfg_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbBaseTest", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void setup_AhbEnvironmentConfig();
  extern virtual function void setup_AhbMasterAgentConfig();
  extern virtual function void setup_AhbSlaveAgentConfig();
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
  setup_AhbEnvironmentConfig();
  ahb_env_h = AhbEnvironment::type_id::create("AhbEnvironment",this);
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function : setup_AhbEnvironmentConfig
//  It calls the master agent config setup and slave agent config steup functions
//--------------------------------------------------------------------------------------------
function void AhbBaseTest::setup_AhbEnvironmentConfig();
  ahb_env_cfg_h = AhbEnvironmentConfig::type_id::create("ahb_env_cfg_h");
  ahb_env_cfg_h.no_of_slaves      = NO_OF_SLAVES;
  ahb_env_cfg_h.has_scoreboard    = 1;
  ahb_env_cfg_h.has_virtual_seqr  = 1;

  //Setting up the configuration for master agent
  setup_AhbMasterAgentConfig();

  //Setting the master agent configuration into config_db
   uvm_config_db#(AhbMasterAgentConfig)::set(this,"*master_agent*","AhbMasterAgentConfig",
                                               ahb_env_cfg_h.ahb_master_agent_cfg_h);
 //Displaying the master agent configuration
  `uvm_info(get_type_name(),$sformatf("\nAHB_MASTER_AGENT_CONFIG\n%s",ahb_env_cfg_h.ahb_master_agent_cfg_h.sprint()),UVM_LOW);

  setup_AhbSlaveAgentConfig();

  uvm_config_db#(AhbEnvironmentConfig)::set(this,"*","AhbEnvironmentConfig",ahb_env_cfg_h);
  `uvm_info(get_type_name(),$sformatf("\nAHB_ENV_CONFIG\n%s",ahb_env_cfg_h.sprint()),UVM_LOW);

endfunction : setup_AhbEnvironmentConfig
//--------------------------------------------------------------------------------------------
// Function : setup_AhbMasterAgentConfig
//  Sets the configurations to the corresponding variables in ahb master agent config
//  Creates the master agent config
//  Sets ahb master agent config into configdb 
//--------------------------------------------------------------------------------------------
function void AhbBaseTest::setup_AhbMasterAgentConfig();
  bit [63:0]local_min_address;
  bit [63:0]local_max_address;
  
  ahb_env_cfg_h.ahb_master_agent_cfg_h = AhbMasterAgentConfig::type_id::create("AhbMasterAgentConfig");
  
  if(MASTER_AGENT_ACTIVE === 1) begin
    ahb_env_cfg_h.ahb_master_agent_cfg_h.is_active = uvm_active_passive_enum'(UVM_ACTIVE);
  end
  else begin
    ahb_env_cfg_h.ahb_master_agent_cfg_h.is_active = uvm_active_passive_enum'(UVM_PASSIVE);
  end
  ahb_env_cfg_h.ahb_master_agent_cfg_h.no_of_slaves = NO_OF_SLAVES;
  ahb_env_cfg_h.ahb_master_agent_cfg_h.has_coverage = 1;

  for(int i =0; i<NO_OF_SLAVES; i++) begin
    if(i == 0) begin  
      ahb_env_cfg_h.ahb_master_agent_cfg_h.master_min_addr_range(i,0);
      local_min_address = ahb_env_cfg_h.ahb_master_agent_cfg_h.master_min_addr_range_array[i];
      
      ahb_env_cfg_h.ahb_master_agent_cfg_h.master_max_addr_range(i,2**(SLAVE_MEMORY_SIZE)-1 );
      local_max_address = ahb_env_cfg_h.ahb_master_agent_cfg_h.master_max_addr_range_array[i];
    end
    else begin
      ahb_env_cfg_h.ahb_master_agent_cfg_h.master_min_addr_range(i,local_max_address + SLAVE_MEMORY_GAP);
      local_min_address = ahb_env_cfg_h.ahb_master_agent_cfg_h.master_min_addr_range_array[i];
      
      ahb_env_cfg_h.ahb_master_agent_cfg_h.master_max_addr_range(i,local_max_address+2**(SLAVE_MEMORY_SIZE)-1 + SLAVE_MEMORY_GAP);
      local_max_address = ahb_env_cfg_h.ahb_master_agent_cfg_h.master_max_addr_range_array[i];
    end
  end
endfunction : setup_AhbMasterAgentConfig
//--------------------------------------------------------------------------------------------
// Function : setup_AhbSlaveAgentConfig
//  It calls the master agent config setup and slave agent config steup functions
//--------------------------------------------------------------------------------------------
    
function void AhbBaseTest::setup_AhbSlaveAgentConfig();
  ahb_env_cfg_h.ahb_slave_agent_cfg_h = new[ahb_env_cfg_h.no_of_slaves];
  foreach(ahb_env_cfg_h.ahb_slave_agent_cfg_h[i]) begin
    ahb_env_cfg_h.ahb_slave_agent_cfg_h[i] = AhbSlaveAgentConfig::type_id::create($sformatf("AhbSlaveAgentConfig[%0d]",i));
    ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].slave_id       = i;
    ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].slave_selected = 0;
    ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].min_address    = ahb_env_cfg_h.ahb_master_agent_cfg_h.master_min_addr_range_array[i];
    ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].max_address    = ahb_env_cfg_h.ahb_master_agent_cfg_h.master_max_addr_range_array[i];
    if(SLAVE_AGENT_ACTIVE === 1) begin
      ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].is_active = uvm_active_passive_enum'(UVM_ACTIVE);
    end
    else begin
      ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].is_active = uvm_active_passive_enum'(UVM_PASSIVE);
    end
    ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].has_coverage = 1; 
    uvm_config_db #(AhbSlaveAgentConfig)::set(this,$sformatf("*env*"),$sformatf("AhbSlaveAgentConfig[%0d]",i),
    ahb_env_cfg_h.ahb_slave_agent_cfg_h[i]);
    `uvm_info(get_type_name(),$sformatf("\nAHB_SLAVE_CONFIG[%0d]\n%s",i,ahb_env_cfg_h.ahb_slave_agent_cfg_h[i].sprint()),UVM_LOW);
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

  phase.raise_objection(this);
  super.run_phase(phase);
  #100;
  phase.drop_objection(this);

endtask : run_phase

`endif

