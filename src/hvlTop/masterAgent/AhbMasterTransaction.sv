`ifndef AHBMASTERTRANSACTION_INCLUDED_
`define AHBMASTERTRANSACTION_INCLUDED_

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
  rand ahbBurstEnum HBURST;

  // Variable : HMASTLOCK
  // Indicates a locked sequence
  rand bit HMASTLOCK;

  // Variable : HPROT
  // Protection control signal
  rand ahbProtectionEnum HPROT;

  // Variable : HSIZE
  // Indicates the size of a transfer
  rand ahbHsizeEnum HSIZE;

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
  rand ahbTransferEnum HTRANS;

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
 // ahbRespEnum HEXOKAY;

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
 AhbMasterTransaction ahbMasterTransactionCopyObject;

  if(!$cast(ahbMasterTransactionCopyObject,rhs)) begin
    `uvm_fatal("do_copy","cast of the rhs object failed")
  end
  super.do_copy(rhs);

HADDR      = ahbMasterTransactionCopyObject.HADDR;
HSELx      = ahbMasterTransactionCopyObject.HSELx;
HBURST     = ahbMasterTransactionCopyObject.HBURST;
HMASTLOCK  = ahbMasterTransactionCopyObject.HMASTLOCK;
HPROT      = ahbMasterTransactionCopyObject.HPROT;
HSIZE      = ahbMasterTransactionCopyObject.HSIZE;
HNONSEC    = ahbMasterTransactionCopyObject.HNONSEC;
HEXCL      = ahbMasterTransactionCopyObject.HEXCL;
HMASTER    = ahbMasterTransactionCopyObject.HMASTER;
HTRANS     = ahbMasterTransactionCopyObject.HTRANS;
HWDATA     = ahbMasterTransactionCopyObject.HWDATA;
HWSTRB     = ahbMasterTransactionCopyObject.HWSTRB;
HWRITE     = ahbMasterTransactionCopyObject.HWRITE;

// Outputs for read transactions
HRDATA     = ahbMasterTransactionCopyObject.HRDATA;
HREADYOUT  = ahbMasterTransactionCopyObject.HREADYOUT;
HRESP      = ahbMasterTransactionCopyObject.HRESP;
//HEXOKAY    = ahbMasterTransactionCopyObject.HEXOKAY;
HREADY     = ahbMasterTransactionCopyObject.HREADY;

endfunction : do_copy

//--------------------------------------------------------------------------------------------
// Function: do_compare
//  Compare method is implemented using handle rhs
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function bit AhbMasterTransaction::do_compare (uvm_object rhs, uvm_comparer comparer);
  AhbMasterTransaction ahbMasterTransactionCompareObject;

 if(!$cast(ahbMasterTransactionCompareObject,rhs)) begin
  `uvm_fatal("FATAL_AHB_MASTER_TX_DO_COMPARE_FAILED","cast of the rhs object failed")
    return 0;
  end

 return super.do_compare(ahbMasterTransactionCompareObject, comparer) &&
HADDR    == ahbMasterTransactionCompareObject.HADDR    &&
HSELx    == ahbMasterTransactionCompareObject.HSELx    &&
HBURST   == ahbMasterTransactionCompareObject.HBURST   &&
HMASTLOCK == ahbMasterTransactionCompareObject.HMASTLOCK &&
HPROT    ==ahbMasterTransactionCompareObject.HPROT    &&
HSIZE    == ahbMasterTransactionCompareObject.HSIZE    &&
HNONSEC  == ahbMasterTransactionCompareObject.HNONSEC  &&
HEXCL    == ahbMasterTransactionCompareObject.HEXCL    &&
HMASTER  == ahbMasterTransactionCompareObject.HMASTER  &&
HTRANS   == ahbMasterTransactionCompareObject.HTRANS   &&
HWDATA   == ahbMasterTransactionCompareObject.HWDATA   &&
HWSTRB   == ahbMasterTransactionCompareObject.HWSTRB   &&
HWRITE   == ahbMasterTransactionCompareObject.HWRITE   &&
HRDATA   == ahbMasterTransactionCompareObject.HRDATA   &&
HREADYOUT == ahbMasterTransactionCompareObject.HREADYOUT &&
HRESP    == ahbMasterTransactionCompareObject.HRESP    &&
//HEXOKAY  == ahbMasterTransactionCompareObject.HEXOKAY  &&
HREADY   == ahbMasterTransactionCompareObject.HREADY;

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
 printer.print_field ("HMASTLOCK", HMASTLOCK,$bits(HMASTLOCK),UVM_HEX);
printer.print_string ("HPROT", HPROT.name());
printer.print_string ("HSIZE", HSIZE.name());
 printer.print_field ("HNONSEC", HNONSEC,$bits(HNONSEC),UVM_HEX);
 printer.print_field ("HEXCL", HEXCL,$bits(HEXCL),UVM_HEX);
printer.print_field  ("HMASTER", HMASTER, $bits(HMASTER), UVM_DEC);
printer.print_string ("HTRANS", HTRANS.name());
printer.print_field  ("HWDATA", HWDATA, $bits(HWDATA), UVM_HEX);
printer.print_field  ("HWSTRB", HWSTRB, $bits(HWSTRB), UVM_BIN);
printer.print_string ("HWRITE", HWRITE, $bits(HWRITE), UVM_BIN);
printer.print_field  ("HRDATA", HRDATA, $bits(HRDATA), UVM_HEX);
 printer.print_field ("HREADYOUT", HREADYOUT,$bits(HREADYOUT),UVM_HEX);
printer.print_string ("HRESP", HRESP.name());
//printer.print_string ("HEXOKAY", HEXOKAY.name());
 printer.print_field ("HREADY", HREADY,$bits(HREADY),UVM_HEX);


endfunction : do_print

//--------------------------------------------------------------------------------------------
// Function : post_randomize
// Selects the address based on the slave selected
//--------------------------------------------------------------------------------------------
function void AhbMasterTransaction::post_randomize();
  //Logic
endfunction : post_randomize

`endif
