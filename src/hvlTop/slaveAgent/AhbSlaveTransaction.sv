`ifndef AHBSLAVETRANSACTION_INCLUDED_
`define AHBSLAVETRANSACTION_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveTransaction.
//  This class holds the data items required for the slave-side transaction 
//  and methods to manipulate those data items.
//--------------------------------------------------------------------------------------------
class AhbSlaveTransaction extends uvm_sequence_item;
  `uvm_object_utils(AhbSlaveTransaction)

  // Variable : haddr
// Byte address of the transfer
bit [ADDR_WIDTH-1:0] haddr;

// Variable : hselx
// Indicates the number of slaves
bit [NO_OF_SLAVES-1:0] hselx;
  
// Variable : hburst
// Indicates burst type
ahbBurstEnum hburst;

// Variable : hmastlock
// Indicates a locked sequence
bit hmastlock;

// Variable : hprot
// Protection control signal
ahbProtectionEnum hprot;

// Variable : hsize
// Indicates the size of a transfer
ahbHsizeEnum hsize;

// Variable : hnonsec
// Indicates whether the transfer is Non-secure or Secure
bit hnonsec;

// Variable : hexcl
// Indicates Exclusive Access sequence
bit hexcl;

// Variable : hmaster
// Manager identifier
bit [HMASTER_WIDTH-1:0] hmaster;

// Variable : htrans
// Indicates the transfer type
ahbTransferEnum htrans;

// Variable : hwddata
// Write data bus
bit [DATA_WIDTH-1:0] hwdata;

// Variable : hwstrb
// Write strobes for active byte lanes
bit [(DATA_WIDTH/8)-1:0] hwstrb;

// Variable : hwrite
// Indicates transfer direction (1 = write, 0 = read)
bit hwrite;

// Outputs for slave
// Variable : hrdata
// Read data bus
rand bit [DATA_WIDTH-1:0] hrdata;

// Variable : hreadyout
// Indicates transfer completion for a Subordinate
rand bit hreadyout;

// Variable : hresp
// Transfer response status (0 = OKAY, 1 = ERROR)
rand ahbRespEnum hresp;

// Variable : hexokay
// Indicates Exclusive OKAY status
// rand ahbrespenum hexokay;
  
  // Variable : hready
  // Combined transfer completion for Manager and Subordinate
 rand bit hready;
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
haddr     = ahbSlaveTransaction.haddr;
hselx     = ahbSlaveTransaction.hselx;
hburst    = ahbSlaveTransaction.hburst;
hmastlock = ahbSlaveTransaction.hmastlock;
hprot     = ahbSlaveTransaction.hprot;
hsize     = ahbSlaveTransaction.hsize;
hnonsec   = ahbSlaveTransaction.hnonsec;
hexcl     = ahbSlaveTransaction.hexcl;
hmaster   = ahbSlaveTransaction.hmaster;
htrans    = ahbSlaveTransaction.htrans;
hwdata   = ahbSlaveTransaction.hwdata;
hwstrb    = ahbSlaveTransaction.hwstrb;
hwrite    = ahbSlaveTransaction.hwrite;

// Outputs for slave
hrdata    = ahbSlaveTransaction.hrdata;
hreadyout = ahbSlaveTransaction.hreadyout;
hresp     = ahbSlaveTransaction.hresp;
// hexokay   = ahbSlaveTransaction.hexokay;
hready    = ahbSlaveTransaction.hready;

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
haddr     == ahbSlaveTransaction.haddr     &&
hselx     == ahbSlaveTransaction.hselx     &&
hburst    == ahbSlaveTransaction.hburst    &&
hmastlock == ahbSlaveTransaction.hmastlock &&
hprot     == ahbSlaveTransaction.hprot     &&
hsize     == ahbSlaveTransaction.hsize     &&
hnonsec   == ahbSlaveTransaction.hnonsec   &&
hexcl     == ahbSlaveTransaction.hexcl     &&
hmaster   == ahbSlaveTransaction.hmaster   &&
htrans    == ahbSlaveTransaction.htrans    &&
hwdata   == ahbSlaveTransaction.hwdata   &&
hwstrb    == ahbSlaveTransaction.hwstrb    &&
hwrite    == ahbSlaveTransaction.hwrite    &&
hrdata    == ahbSlaveTransaction.hrdata    &&
hreadyout == ahbSlaveTransaction.hreadyout &&
hresp     == ahbSlaveTransaction.hresp     &&
// && hexokay   == ahbSlaveTransaction.hexokay;
hready    == ahbSlaveTransaction.hready;
endfunction : do_compare

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method to display the data members' values
//
// Parameters:
//  printer - uvm_printer
//--------------------------------------------------------------------------------------------
function void AhbSlaveTransaction::do_print(uvm_printer printer);
printer.print_field  ("haddr", haddr, $bits(haddr), UVM_HEX);
printer.print_field  ("hselx", hselx, $bits(hselx), UVM_BIN);
printer.print_string ("hburst", hburst.name());
printer.print_field ("hmastlock", hmastlock, $bits(hmastlock), UVM_HEX);
printer.print_string ("hprot", hprot.name());
printer.print_string ("hsize", hsize.name());
printer.print_field ("hnonsec", hnonsec, $bits(hnonsec), UVM_HEX);
printer.print_field ("hexcl", hexcl, $bits(hexcl), UVM_HEX);
printer.print_field  ("hmaster", hmaster, $bits(hmaster), UVM_DEC);
printer.print_string ("htrans", htrans.name());
printer.print_field  ("hwddata", hwdata, $bits(hwddata), UVM_HEX);
printer.print_field  ("hwstrb", hwstrb, $bits(hwstrb), UVM_BIN);
printer.print_field ("hwrite", hwrite, $bits(hwrite), UVM_BIN);
printer.print_field  ("hrdata", hrdata, $bits(hrdata), UVM_HEX);
printer.print_field ("hreadyout", hreadyout, $bits(hreadyout), UVM_HEX);
printer.print_string ("hresp", hresp.name());
//printer.print_string ("hexokay", hexokay.name());
printer.print_field ("hready", hready, $bits(hready), UVM_HEX);

endfunction : do_print

//--------------------------------------------------------------------------------------------
// Function : post_randomize
// Handles post-randomization logic for the slave transaction
//--------------------------------------------------------------------------------------------
function void AhbSlaveTransaction::post_randomize();
  //Logic
endfunction : post_randomize

`endif
