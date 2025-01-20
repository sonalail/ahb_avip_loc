`ifndef AHB_MASTER_TRANSACTION_INCLUDED_
`define AHB_MASTER_TRANSACTION_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterTransaction.
//  This class holds the data items required to drive stimulus to dut 
//  and also holds methods that manipulate those data items
//--------------------------------------------------------------------------------------------
 class AhbMasterTransaction extends uvm_sequence_item;
  `uvm_object_utils(AhbMasterTransaction)

  // Variable : HADDR
  // Byte address of the transfer
  rand bit [ADDR_WIDTH-1:0] HADDR;

  //Variable : HSELx
  //Indicates the number of slaves
  rand bit [NO_OF_SLAVES-1:0] HSELx;
  
  // Variable : HBURST
  // Indicates burst type
  rand ahb_burst_e HBURST;

  // Variable : HMASTLOCK
  // Indicates a locked sequence
  rand bit HMASTLOCK;

  // Variable : HPROT
  // Protection control signal
  rand ahb_protection_e HPROT;

  // Variable : HSIZE
  // Indicates the size of a transfer
  rand ahb__e HSIZE;

  // Variable : HNONSEC
  // Indicates whether the transfer is Non-secure or Secure
  rand bit HNONSEC;

  // Variable : HEXCL
  // Indicates Exclusive Access sequence
  rand bit HEXCL;

  // Variable : HMASTER
  // Manager identifier
  rand bit [HMASTER_WIDTH-1:0] HMASTER;

  // Variable : HTRANS
  // Indicates the transfer type
  rand ahb_transfer_e HTRANS;

  // Variable : HWDATA
  // Write data bus
  rand bit [DATA_WIDTH-1:0] HWDATA;

  // Variable : HWSTRB
  // Write strobes for active byte lanes
  rand bit [(DATA_WIDTH/8)-1:0] HWSTRB;

  // Variable : HWRITE
  // Indicates transfer direction (1 = write, 0 = read)
  rand bit HWRITE;

  // Variable : HRDATA
  // Read data bus
  bit [DATA_WIDTH-1:0] HRDATA;

  // Variable : HREADYOUT
  // Indicates transfer completion for a Subordinate
  bit HREADYOUT;

  // Variable : HRESP
  // Transfer response status (0 = OKAY, 1 = ERROR)
  bit HRESP;

  // Variable : HEXOKAY
  // Indicates Exclusive OKAY status
  ahb_resp_e HEXOKAY;

  // Variable : HREADY
  // Combined transfer completion for Manager and Subordinate
  bit HREADY;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new  (string name = "AhbMasterTransaction");
  extern function void do_copy(uvm_object rhs);
  extern function bit  do_compare(uvm_object rhs, uvm_comparer comparer);
  extern function void do_print(uvm_printer printer);
  extern function void post_randomize();

  //-------------------------------------------------------
  // Constraints
  //-------------------------------------------------------

endclass : AhbMasterTransaction

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes the class object
//
// Parameters:
//  name - apb_master_tx
//--------------------------------------------------------------------------------------------
function AhbMasterTransaction::new(string name = "AhbMasterTransaction");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: do_copy
//  Copy method is implemented using handle rhs
//
// Parameters:
//  rhs - uvm_object
//--------------------------------------------------------------------------------------------
function void AhbMasterTransaction::do_copy (uvm_object rhs);
 AhbMasterTransaction ahb_master_tx_copy_obj;

  if(!$cast(apb_master_tx_copy_obj,rhs)) begin
    `uvm_fatal("do_copy","cast of the rhs object failed")
  end
  super.do_copy(rhs);

HADDR      = ahb_master_tx_copy_obj.HADDR;
HSELx      = ahb_master_tx_copy_obj.HSELx;
HBURST     = ahb_master_tx_copy_obj.HBURST;
HMASTLOCK  = ahb_master_tx_copy_obj.HMASTLOCK;
HPROT      = ahb_master_tx_copy_obj.HPROT;
HSIZE      = ahb_master_tx_copy_obj.HSIZE;
HNONSEC    = ahb_master_tx_copy_obj.HNONSEC;
HEXCL      = ahb_master_tx_copy_obj.HEXCL;
HMASTER    = ahb_master_tx_copy_obj.HMASTER;
HTRANS     = ahb_master_tx_copy_obj.HTRANS;
HWDATA     = ahb_master_tx_copy_obj.HWDATA;
HWSTRB     = ahb_master_tx_copy_obj.HWSTRB;
HWRITE     = ahb_master_tx_copy_obj.HWRITE;

// Outputs for read transactions
HRDATA     = ahb_master_tx_copy_obj.HRDATA;
HREADYOUT  = ahb_master_tx_copy_obj.HREADYOUT;
HRESP      = ahb_master_tx_copy_obj.HRESP;
HEXOKAY    = ahb_master_tx_copy_obj.HEXOKAY;
HREADY     = ahb_master_tx_copy_obj.HREADY;

endfunction : do_copy

//--------------------------------------------------------------------------------------------
// Function: do_compare
//  Compare method is implemented using handle rhs
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function bit AhbMasterTransaction::do_compare (uvm_object rhs, uvm_comparer comparer);
  AhbMasterTransaction ahb_master_tx_compare_obj;

 if(!$cast(ahb_master_tx_compare_obj,rhs)) begin
  `uvm_fatal("FATAL_AHB_MASTER_TX_DO_COMPARE_FAILED","cast of the rhs object failed")
    return 0;
  end

 return super.do_compare(ahb_master_tx_compare_obj, comparer) &&
HADDR    == ahb_master_tx_compare_obj.HADDR    &&
HSELx    == ahb_master_tx_compare_obj.HSELx    &&
HBURST   == ahb_master_tx_compare_obj.HBURST   &&
HMASTLOCK == ahb_master_tx_compare_obj.HMASTLOCK &&
HPROT    == ahb_master_tx_compare_obj.HPROT    &&
HSIZE    == ahb_master_tx_compare_obj.HSIZE    &&
HNONSEC  == ahb_master_tx_compare_obj.HNONSEC  &&
HEXCL    == ahb_master_tx_compare_obj.HEXCL    &&
HMASTER  == ahb_master_tx_compare_obj.HMASTER  &&
HTRANS   == ahb_master_tx_compare_obj.HTRANS   &&
HWDATA   == ahb_master_tx_compare_obj.HWDATA   &&
HWSTRB   == ahb_master_tx_compare_obj.HWSTRB   &&
HWRITE   == ahb_master_tx_compare_obj.HWRITE   &&
HRDATA   == ahb_master_tx_compare_obj.HRDATA   &&
HREADYOUT == ahb_master_tx_compare_obj.HREADYOUT &&
HRESP    == ahb_master_tx_compare_obj.HRESP    &&
HEXOKAY  == ahb_master_tx_compare_obj.HEXOKAY  &&
HREADY   == ahb_master_tx_compare_obj.HREADY;

endfunction : do_compare

//--------------------------------------------------------------------------------------------
// Function: do_print method
//  Print method can be added to display the data members values
//
// Parameters:
//  printer - uvm_printer
//--------------------------------------------------------------------------------------------
function void AhbMasterTransaction::do_print(uvm_printer printer);
  
printer.print_field  ("HADDR", HADDR, $bits(HADDR), UVM_HEX);
printer.print_field  ("HSELx", HSELx, $bits(HSELx), UVM_BIN);
printer.print_string ("HBURST", HBURST.name());
printer.print_string ("HMASTLOCK", HMASTLOCK.name());
printer.print_string ("HPROT", HPROT.name());
printer.print_string ("HSIZE", HSIZE.name());
printer.print_string ("HNONSEC", HNONSEC.name());
printer.print_string ("HEXCL", HEXCL.name());
printer.print_field  ("HMASTER", HMASTER, $bits(HMASTER), UVM_DEC);
printer.print_string ("HTRANS", HTRANS.name());
printer.print_field  ("HWDATA", HWDATA, $bits(HWDATA), UVM_HEX);
printer.print_field  ("HWSTRB", HWSTRB, $bits(HWSTRB), UVM_BIN);
printer.print_string ("HWRITE", HWRITE.name());
printer.print_field  ("HRDATA", HRDATA, $bits(HRDATA), UVM_HEX);
printer.print_string ("HREADYOUT", HREADYOUT.name());
printer.print_string ("HRESP", HRESP.name());
printer.print_string ("HEXOKAY", HEXOKAY.name());
printer.print_string ("HREADY", HREADY.name());


endfunction : do_print

//--------------------------------------------------------------------------------------------
// Function : post_randomize
// Selects the address based on the slave selected
//--------------------------------------------------------------------------------------------
function void AhbMasterTransaction::post_randomize();
  //Logic
endfunction : post_randomize

`endif
