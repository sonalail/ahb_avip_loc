 // Code your testbench here
// or browse Examples

`ifndef AhbMasterAgentConfig_INCLUDED_
`define AhbMasterAgentConfig_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterAgentConfig
// Used as the configuration class for ahb_master agent, for configuring number of slaves and number
// of active passive agents to be created
//--------------------------------------------------------------------------------------------
class AhbMasterAgentConfig extends uvm_object;
  `uvm_object_utils(AhbMasterAgentConfig)

  //Variable: is_active
  //Used for creating the agent in either passive or active mode
 // uvm_active_passive_enum is_active = UVM_ACTIVE;  

  //Variable: NO_OF_SLAVES
  //Used for specifying the number of slaves connected to this ahb_master over ahb interface
  int NO_OF_SLAVES;

  //Variable: has_coverage
  //Used for enabling the master agent coverage
 // bit has_coverage;

  //Variable: master_memory
  //Memory decleration for master to store the data of each slave
  bit [ADDRESS_WIDTH-1:0]paddr;

  //Variable : master_memory
  //Used to store all the data from the slaves
  //Each location of the master memory stores 8 bit data
 // bit [MEMORY_WIDTH-1:0]master_memory[(SLAVE_MEMORY_SIZE+SLAVE_MEMORY_GAP)*NO_OF_SLAVES:0];

  //Variable : master_min_array
  //An associative array used to store the min address ranges of every slave
  //Index - type    - int
  //        stores  - slave number
  //Value - stores the minimum address range of that slave.
 // bit [ADDRESS_WIDTH-1:0]master_min_addr_range_array[int];

  //Variable : master_max_array
  //An associative array used to store the max address ranges of every slave
  //Index - type    - int
  //        stores  - slave number
  //Value - stores the maximum address range of that slave.
 // bit [ADDRESS_WIDTH-1:0]master_max_addr_range_array[int];

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterAgentConfig");
  extern function void do_print(uvm_printer printer);
  //extern function void master_min_addr_range(int slave_number, bit [ADDRESS_WIDTH-1:0]slave_min_address_range);
  //extern function void master_max_addr_range(int slave_number, bit [ADDRESS_WIDTH-1:0]slave_max_address_range);

endclass : AhbMasterAgentConfig

//--------------------------------------------------------------------------------------------
// Construct: new
// Initializes memory for new object
//
// Parameters:
//  name - AhbMasterAgentConfig
//--------------------------------------------------------------------------------------------
function AhbMasterAgentConfig::new(string name = "AhbMasterAgentConfig");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//
// Parameters:
//  printer - uvm_printer
//--------------------------------------------------------------------------------------------
function void AhbMasterAgentConfig::do_print(uvm_printer printer);
  super.do_print(printer);

//  printer.print_field ("is_active",    is_active,    $bits(is_active),    UVM_DEC);
 // printer.print_field ("has_coverage", has_coverage, $bits(has_coverage), UVM_DEC);
  printer.print_field ("NO_OF_SLAVES", NO_OF_SLAVES, $bits(NO_OF_SLAVES), UVM_DEC);

endfunction : do_print

//--------------------------------------------------------------------------------------------
// Function : master_max_addr_range_array
// Used to store the maximum address ranges of the slaves in the array
// Parameters :
//  slave_number            - int
//  slave_max_address_range - bit [63:0]
//--------------------------------------------------------------------------------------------
//function void AhbMasterAgentConfig::master_max_addr_range(int slave_number, bit[ADDRESS_WIDTH-1:0]slave_max_address_range);
//  master_max_addr_range_array[slave_number] = slave_max_address_range;
//endfunction : master_max_addr_range

//--------------------------------------------------------------------------------------------
// Function : master_min_addr_range_array
// Used to store the minimum address ranges of the slaves in the array
// Parameters :
//  slave_number            - int
//  slave_min_address_range - bit [63:0]
//--------------------------------------------------------------------------------------------
//function void AhbMasterAgentConfig::master_min_addr_range(int slave_number, bit[ADDRESS_WIDTH-1:0]slave_min_address_range);
//  master_min_addr_range_array[slave_number] = slave_min_address_range;
//endfunction : master_min_addr_range

`endif

