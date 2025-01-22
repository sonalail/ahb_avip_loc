`ifndef AHBSLAVETRANSACTION_INCLUDED_
`define AHBSLAVETRANSACTION_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveTransaction.
//  This class holds the data items required for the slave-side transaction 
//  and methods to manipulate those data items.
//--------------------------------------------------------------------------------------------
class AhbSlaveTransaction extends uvm_sequence_item;
  `uvm_object_utils(AhbSlaveTransaction)

  // Variable : HADDR
  // Byte address of the transfer
  bit [ADDR_WIDTH-1:0] HADDR;

  // Variable : HSELx
  // Indicates the number of slaves
  bit [NO_OF_SLAVES-1:0] HSELx;
  
  // Variable : HBURST
  // Indicates burst type
  ahbBurstEnum HBURST;

  // Variable : HMASTLOCK
  // Indicates a locked sequence
  bit HMASTLOCK;

  // Variable : HPROT
  // Protection control signal
  ahbProtectionEnum HPROT;

  // Variable : HSIZE
  // Indicates the size of a transfer
  ahbHsizeEnum HSIZE;

  // Variable : HNONSEC
  // Indicates whether the transfer is Non-secure or Secure
  bit HNONSEC;

  // Variable : HEXCL
  // Indicates Exclusive Access sequence
  bit HEXCL;

  // Variable : HMASTER
  // Manager identifier
  bit [HMASTER_WIDTH-1:0] HMASTER;

  // Variable : HTRANS
  // Indicates the transfer type
  ahbTransferEnum HTRANS;

  // Variable : HWDATA
  // Write data bus
  bit [DATA_WIDTH-1:0] HWDATA;

  // Variable : HWSTRB
  // Write strobes for active byte lanes
  bit [(DATA_WIDTH/8)-1:0] HWSTRB;

  // Variable : HWRITE
  // Indicates transfer direction (1 = write, 0 = read)
  bit HWRITE;

  // Outputs for slave
  // Variable : HRDATA
  // Read data bus
  rand bit [DATA_WIDTH-1:0] HRDATA;

  // Variable : HREADYOUT
  // Indicates transfer completion for a Subordinate
  rand bit HREADYOUT;

  // Variable : HRESP
  // Transfer response status (0 = OKAY, 1 = ERROR)
  rand bit HRESP;

  // Variable : HEXOKAY
  // Indicates Exclusive OKAY status
  rand ahbRespEnum HEXOKAY;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveTransaction");
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
  extern function void do_print(uvm_printer printer);
  extern function void post_randomize();

  //-------------------------------------------------------
  // Constraints
  //-------------------------------------------------------

endclass : AhbSlaveTransaction

//--------------------------------------------------------------------------------------------
// Construct: new
// Initializes the class object
//
// Parameters:
//  name - AhbSlaveTransaction
//--------------------------------------------------------------------------------------------
function AhbSlaveTransaction::new(string name = "AhbSlaveTransaction");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: do_copy
// Copy method is implemented using handle rhs
//
// Parameters:
//  rhs - uvm_object
//--------------------------------------------------------------------------------------------
function void AhbSlaveTransaction::do_copy(uvm_object rhs);
  AhbSlaveTransaction ahbSlaveTransaction;

  if (!$cast(ahbSlaveTransaction, rhs)) begin
    `uvm_fatal("do_copy", "cast of the rhs object failed")
  end
  super.do_copy(rhs);

  // Inputs for slave
  HADDR     = ahbSlaveTransaction.HADDR;
  HSELx     = ahbSlaveTransaction.HSELx;
  HBURST    = ahbSlaveTransaction.HBURST;
  HMASTLOCK = ahbSlaveTransaction.HMASTLOCK;
  HPROT     = ahbSlaveTransaction.HPROT;
  HSIZE     = ahbSlaveTransaction.HSIZE;
  HNONSEC   = ahbSlaveTransaction.HNONSEC;
  HEXCL     = ahbSlaveTransaction.HEXCL;
  HMASTER   = ahbSlaveTransaction.HMASTER;
  HTRANS    = ahbSlaveTransaction.HTRANS;
  HWDATA    = ahbSlaveTransaction.HWDATA;
  HWSTRB    = ahbSlaveTransaction.HWSTRB;
  HWRITE    = ahbSlaveTransaction.HWRITE;

  // Outputs for slave
  HRDATA    = ahbSlaveTransaction.HRDATA;
  HREADYOUT = ahbSlaveTransaction.HREADYOUT;
  HRESP     = ahbSlaveTransaction.HRESP;
  HEXOKAY   = ahbSlaveTransaction.HEXOKAY;

endfunction : do_copy

//--------------------------------------------------------------------------------------------
// Function: do_compare
// Compare method is implemented using handle rhs
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function bit AhbSlaveTransaction::do_compare(uvm_object rhs, uvm_comparer comparer);
  AhbSlaveTransaction ahbSlaveTransaction;

  if (!$cast(ahbSlaveTransaction, rhs)) begin
    `uvm_fatal("FATAL_AHB_SLAVE_TX_DO_COMPARE_FAILED", "cast of the rhs object failed")
    return 0;
  end

  return super.do_compare(ahbSlaveTransaction, comparer) &&
         HADDR     == ahbSlaveTransaction.HADDR     &&
         HSELx     == ahbSlaveTransaction.HSELx     &&
         HBURST    == ahbSlaveTransaction.HBURST    &&
         HMASTLOCK == ahbSlaveTransaction.HMASTLOCK &&
         HPROT     == ahbSlaveTransaction.HPROT     &&
         HSIZE     == ahbSlaveTransaction.HSIZE     &&
         HNONSEC   == ahbSlaveTransaction.HNONSEC   &&
         HEXCL     == ahbSlaveTransaction.HEXCL     &&
         HMASTER   == ahbSlaveTransaction.HMASTER   &&
         HTRANS    == ahbSlaveTransaction.HTRANS    &&
         HWDATA    == ahbSlaveTransaction.HWDATA    &&
         HWSTRB    == ahbSlaveTransaction.HWSTRB    &&
         HWRITE    == ahbSlaveTransaction.HWRITE    &&
         HRDATA    == ahbSlaveTransaction.HRDATA    &&
         HREADYOUT == ahbSlaveTransaction.HREADYOUT &&
         HRESP     == ahbSlaveTransaction.HRESP     &&
         HEXOKAY   == ahbSlaveTransaction.HEXOKAY;
endfunction : do_compare

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method to display the data members' values
//
// Parameters:
//  printer - uvm_printer
//--------------------------------------------------------------------------------------------
function void AhbSlaveTransaction::do_print(uvm_printer printer);
 printer.print_field  ("HADDR", HADDR, $bits(HADDR), UVM_HEX);
printer.print_field  ("HSELx", HSELx, $bits(HSELx), UVM_BIN);
 printer.print_string ("HBURST", HBURST.name());
 printer.print_field ("HMASTLOCK", HMASTLOCK,$bits(HMASTLOCK),UVM_HEX);
printer.print_string ("HPROT", HPROT.name());
printer.print_string ("HSIZE", HSIZE.name());
 printer.print_field ("HNONSEC", HNONSEC,$bits(HNONSEC),UVM_HEX);
 printer.print_field ("HEXCL", HEXCL,$bits(HEXCL),UVM_HEX);
printer.print_field  ("HMASTER", HMASTER, $bits(HMASTER), UVM_DEC);
printer.print_string ("HTRANS", HTRANS.name());
printer.print_field  ("HWDATA", HWDATA, $bits(HWDATA), UVM_HEX);
printer.print_field  ("HWSTRB", HWSTRB, $bits(HWSTRB), UVM_BIN);
printer.print_field ("HWRITE", HWRITE, $bits(HWRITE), UVM_BIN);
printer.print_field  ("HRDATA", HRDATA, $bits(HRDATA), UVM_HEX);
 printer.print_field ("HREADYOUT", HREADYOUT,$bits(HREADYOUT),UVM_HEX);
 printer.print_string ("HRESP", HRESP.name());
//printer.print_string ("HEXOKAY", HEXOKAY.name());
 printer.print_field ("HREADY", HREADY,$bits(HREADY),UVM_HEX);
endfunction : do_print

//--------------------------------------------------------------------------------------------
// Function : post_randomize
// Handles post-randomization logic for the slave transaction
//--------------------------------------------------------------------------------------------
function void AhbSlaveTransaction::post_randomize();
  //Logic
endfunction : post_randomize

`endif
