`ifndef AHBBASETEST_INCLUDED_
`define AHBBASETEST_INCLUDED_

class AhbBaseTest extends uvm_test;
  `uvm_component_utils(AhbBaseTest)
  
   AhbEnvironment ahbEnvironment;

   AhbEnvironmentConfig ahbEnvironmentConfig;

  extern function new(string name = "AhbBaseTest", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void setupAhbEnvironmentConfig();
  extern virtual function void setupAhbMasterAgentConfig();
  extern virtual function void setupAhbSlaveAgentConfig();
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : AhbBaseTest

function AhbBaseTest::new(string name = "AhbBaseTest",uvm_component parent = null);
  super.new(name, parent);
endfunction : new

function void AhbBaseTest::build_phase(uvm_phase phase);
  super.build_phase(phase);
  setupAhbEnvironmentConfig();
  ahbEnvironment = AhbEnvironment::type_id::create("ahbEnvironment",this);
endfunction : build_phase

function void AhbBaseTest::setupAhbEnvironmentConfig();
  ahbEnvironmentConfig = AhbEnvironmentConfig::type_id::create("ahbEnvironmentConfig");
  ahbEnvironmentConfig.noOfSlaves      = NO_OF_SLAVES;
  ahbEnvironmentConfig.hasScoreboard    = 1;
  ahbEnvironmentConfig.hasVirtualSequencer  = 1;

   setupAhbMasterAgentConfig();

   uvm_config_db#(AhbMasterAgentConfig)::set(this,"*MasterAgent*","AhbMasterAgentConfig",ahbEnvironmentConfig.ahbMasterAgentConfig);
 // `uvm_info(get_type_name(),$sformatf("\nAHB_MASTER_AGENT_CONFIG\n%s",ahbEnvironmentConfig.ahbMasterAgentConfig.sprint()),UVM_LOW);
 
// ahbEnvironmentConfig.ahbSlaveAgentConfig = new[ahbEnvironmentConfig.ahbSlaveAgentConfig.noOfSlaves];
 //  foreach(ahbEnvironmentConfig.ahbSlaveAgentConfig[i]) begin
 // 	 ahbEnvironmentConfig.ahbSlaveAgentConfig[i] = AhbSlaveAgentConfig::type_id::create($sformatf("AhbSlaveAgentConfig[%0d]",i));
  // end

  setupAhbSlaveAgentConfig();
 
  uvm_config_db#(AhbEnvironmentConfig)::set(this,"*","AhbEnvironmentConfig",ahbEnvironmentConfig);
  `uvm_info(get_type_name(),$sformatf("\nAHB_ENV_CONFIG\n%s",ahbEnvironmentConfig.sprint()),UVM_LOW);

endfunction : setupAhbEnvironmentConfig

function void AhbBaseTest::setupAhbMasterAgentConfig();
  // bit [63:0]local_min_address;
  // bit [63:0]local_max_address;
  
  ahbEnvironmentConfig.ahbMasterAgentConfig = new[ahbEnvironmentConfig.noOfMasters];
  foreach(ahbEnvironmentConfig.ahbMasterAgentConfig[i]) begin
    ahbEnvironmentConfig.ahbMasterAgentConfig[i] = AhbMasterAgentConfig::type_id::create($sformatf("AhbMasterAgentConfig[%0d]",i));
 
   if(MASTER_AGENT_ACTIVE === 1) begin
     ahbEnvironmentConfig.ahbMasterAgentConfig[i].is_active = uvm_active_passive_enum'(UVM_ACTIVE);
  end
  else begin
    ahbEnvironmentConfig.ahbMasterAgentConfig[i].is_active = uvm_active_passive_enum'(UVM_PASSIVE);
  end

   ahbEnvironmentConfig.ahbMasterAgentConfig[i].hasCoverage = 1; 
  uvm_config_db #(AhbMasterAgentConfig)::set(this,$sformatf("*env*"),$sformatf("AhbMasterAgentConfig[%0d]",i),
    ahbEnvironmentConfig.ahbMasterAgentConfig[i]);
  `uvm_info(get_type_name(),$sformatf("\nAHB_MASTER_CONFIG[%0d]\n%s",i,ahbEnvironmentConfig.ahbMasterAgentConfig[i].sprint()),UVM_LOW);
   end

 // ahbEnvironmentConfig.ahbMasterAgentConfig.noOfSlaves = NO_OF_SLAVES;
  

  // for(int i =0; i<NO_OF_SLAVES; i++) begin
  //   if(i == 0) begin  
  //     ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range(i,0);
  //     local_min_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range_array[i];
      
  //     ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range(i,2**(SLAVE_MEMORY_SIZE)-1 );
  //     local_max_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range_array[i];
  //   end
  //   else begin
  //     ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range(i,local_max_address + SLAVE_MEMORY_GAP);
  //     local_min_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range_array[i];
      
  //     ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range(i,local_max_address+2**(SLAVE_MEMORY_SIZE)-1 + SLAVE_MEMORY_GAP);
  //     local_max_address = ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range_array[i];
  //   end
  // end
endfunction : setupAhbMasterAgentConfig

function void AhbBaseTest::setupAhbSlaveAgentConfig();
 ahbEnvironmentConfig.ahbSlaveAgentConfig = new[ahbEnvironmentConfig.noOfSlaves];
   foreach(ahbEnvironmentConfig.ahbSlaveAgentConfig[i]) begin
     ahbEnvironmentConfig.ahbSlaveAgentConfig[i] = AhbSlaveAgentConfig::type_id::create($sformatf("AhbSlaveAgentConfig[%0d]",i));
  //   ahbEnvironmentConfig.ahbSlaveAgentConfig[i].slave_id       = i;
  //   ahbEnvironmentConfig.ahbSlaveAgentConfig[i].slave_selected = 0;
  //   ahbEnvironmentConfig.ahbSlaveAgentConfig[i].min_address    = ahbEnvironmentConfig.ahbMasterAgentConfig.master_min_addr_range_array[i];
  //   ahbEnvironmentConfig.ahbSlaveAgentConfig[i].max_address    = ahbEnvironmentConfig.ahbMasterAgentConfig.master_max_addr_range_array[i];
    if(SLAVE_AGENT_ACTIVE === 1) begin
      ahbEnvironmentConfig.ahbSlaveAgentConfig[i].is_active = uvm_active_passive_enum'(UVM_ACTIVE);
    end
    else begin
      ahbEnvironmentConfig.ahbSlaveAgentConfig[i].is_active = uvm_active_passive_enum'(UVM_PASSIVE);
    end
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i].hasCoverage = 1; 
    uvm_config_db #(AhbSlaveAgentConfig)::set(this,$sformatf("*env*"),$sformatf("AhbSlaveAgentConfig[%0d]",i),
    ahbEnvironmentConfig.ahbSlaveAgentConfig[i]);
    `uvm_info(get_type_name(),$sformatf("\nAHB_SLAVE_CONFIG[%0d]\n%s",i,ahbEnvironmentConfig.ahbSlaveAgentConfig[i].sprint()),UVM_LOW);
  end

endfunction : setupAhbSlaveAgentConfig

function void AhbBaseTest::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  uvm_top.print_topology();
endfunction  : end_of_elaboration_phase

task AhbBaseTest::run_phase(uvm_phase phase);
  `uvm_info(get_type_name(),$sformatf("Inside run phase of test"),UVM_LOW);
  phase.raise_objection(this);
  super.run_phase(phase);
  #100;
  phase.drop_objection(this);

endtask : run_phase

`endif

