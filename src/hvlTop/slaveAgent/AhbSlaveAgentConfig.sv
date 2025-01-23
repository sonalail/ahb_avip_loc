`ifndef AHBSLAVEAGENTCONFIG_INCLUDED_
`define AHBSLAVEAGENTCONFIG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveAgentConfig
//  Used as the configuration class for slave agent and it's components
//--------------------------------------------------------------------------------------------
class AhbSlaveAgentConfig extends uvm_object;
  
  `uvm_object_utils(AhbSlaveAgentConfig) 
  
  //Variable: is_active
  //Used to declare whether the agent is active or passive
  uvm_active_passive_enum is_active = UVM_ACTIVE;
  
  //Variable: slave_id
  //Gives the slave id
  //int slave_id;
  
  //Variable: hasCoverage
  //Used to set whether we need to create coverage or not
  bit hasCoverage;
  
  //Variable: slave_selected
  //Used to represent that this slave is selected
  //bit slave_selected;

  //Variable: max_address
  //Used to store the maximum address value of this slave
  //bit [ADDRESS_WIDTH-1:0]max_address;

  //Variable: min_address
  //Used to store the minimum address value of this slave
  //bit [ADDRESS_WIDTH-1:0]min_address;
  
  //Variable: slave_memory
  //Declaration of slave_memory to store the data from master
  //bit [7:0]slave_memory[longint];
  
  //Variable: paddr
  //Used to indicate the slave address
  bit [DATA_WIDTH-1:0]haddr;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveAgentConfig");
  extern function void do_print(uvm_printer printer);
//   extern virtual task slaveMemoryTask(bit [HADDR-1:0]slave_address, bit [DATA_WIDTH-1:0]data); 

endclass : AhbSlaveAgentConfig

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - AhbSlaveAgentConfig
//--------------------------------------------------------------------------------------------
function AhbSlaveAgentConfig::new(string name = "AhbSlaveAgentConfig");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: do_print method
//  Print method can be added to display the data members values
//--------------------------------------------------------------------------------------------
function void AhbSlaveAgentConfig::do_print(uvm_printer printer);
  super.do_print(printer);

   printer.print_string ("is_active",is_active.name());
   //printer.print_field ("slave_id",slave_id,$bits(slave_id),UVM_DEC);
  printer.print_field ("hasCoverage",hasCoverage,$bits(hasCoverage),UVM_DEC);
  //printer.print_field ("max_address",max_address,$bits(max_address),UVM_HEX);
  //printer.print_field ("min_address",min_address,$bits(max_address),UVM_HEX);
  
endfunction : do_print

//--------------------------------------------------------------------------------------------
// Task : slaveMemoryTask
//  Used to store the slave data into the slave memory
// 
// Parameters :
//  slave_address   - bit [ADDRESS_WIDTH-1:0]
//  data            - bit [DATA_WIDTH-1:0]
//--------------------------------------------------------------------------------------------
//    task AhbSlaveAgentConfig::slaveMemoryTask(bit [HADDR-1:0]slave_address, bit [DATA_WIDTH-1:0]data);
//  slave_memory[slave_address] = data;
//endtask : slaveMemoryTask

`endif
