`ifndef AHBMASTERTRANSACTION_INCLUDED_
`define AHBMASTERTRANSACTION_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterTransaction.
//  This class holds the data items required to drive stimulus to dut 
//  and also holds methods that manipulate those data items
//--------------------------------------------------------------------------------------------
 class AhbMasterTransaction extends uvm_sequence_item;
  `uvm_object_utils(AhbMasterTransaction)

  // Variable : haddr
  // Byte address of the transfer
  rand bit [ADDR_WIDTH-1:0] haddr;

  //Variable : hselx
  //Indicates the number of slaves
  rand bit [NO_OF_SLAVES-1:0] hselx;
  
  // Variable : hburst
  // Indicates burst type
  rand ahbBurstEnum hburst;

  // Variable : hmastlock
  // Indicates a locked sequence
  rand bit hmastlock;

  // Variable : hprot
  // Protection control signal
  rand ahbProtectionEnum hprot;

  // Variable : hsize
  // Indicates the size of a transfer
  rand ahbHsizeEnum hsize;

  // Variable : hnonsec
  // Indicates whether the transfer is Non-secure or Secure
  rand bit hnonsec;

  // Variable : hexcl
  // Indicates Exclusive Access sequence
  rand bit hexcl;

  // Variable : hmaster
  // Manager identifier
  rand bit [HMASTER_WIDTH-1:0] hmaster;

  // Variable : htrans
  // Indicates the transfer type
  rand ahbTransferEnum htrans;

  // Variable : hwdata
  // Write data bus
  rand bit [DATA_WIDTH-1:0] hwdata;

  // Variable : hwstrb
  // Write strobes for active byte lanes
  rand bit [(DATA_WIDTH/8)-1:0] hwstrb;

  // Variable : hwrite
  // Indicates transfer direction (1 = write, 0 = read)
  rand bit hwrite;

  // Variable : hrdata
  // Read data bus
  bit [DATA_WIDTH-1:0] hrdata;

  // Variable : hreadyout
  // Indicates transfer completion for a Subordinate
  bit hreadyout;

  // Variable : hresp
  // Transfer response status (0 = OKAY, 1 = ERROR)
  rand ahbRespEnum hresp;

  // Variable : hexokay
  // Indicates Exclusive OKAY status
 // ahbRespEnum hexokay;

  // Variable : hready
  // Combined transfer completion for Manager and Subordinate
  bit hready;
  
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
 AhbMasterTransaction ahbMasterTransaction;

  if(!$cast(ahbMasterTransaction,rhs)) begin
    `uvm_fatal("do_copy","cast of the rhs object failed")
  end
  super.do_copy(rhs);

haddr      = ahbMasterTransaction.haddr;
hselx      = ahbMasterTransaction.hselx;
hburst     = ahbMasterTransaction.hburst;
hmastlock  = ahbMasterTransaction.hmastlock;
hprot      = ahbMasterTransaction.hprot;
hsize      = ahbMasterTransaction.hsize;
hnonsec    = ahbMasterTransaction.hnonsec;
hexcl      = ahbMasterTransaction.hexcl;
hmaster    = ahbMasterTransaction.hmaster;
htrans     = ahbMasterTransaction.htrans;
hwdata     = ahbMasterTransaction.hwdata;
hwstrb     = ahbMasterTransaction.hwstrb;
hwrite     = ahbMasterTransaction.hwrite;

// Outputs for read transactions
hrdata     = ahbMasterTransaction.hrdata;
hreadyout  = ahbMasterTransaction.hreadyout;
hresp      = ahbMasterTransaction.hresp;
//hexokay    = ahbMasterTransaction.hexokay;
hready     = ahbMasterTransaction.hready;

endfunction : do_copy

//--------------------------------------------------------------------------------------------
// Function: do_compare
//  Compare method is implemented using handle rhs
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function bit AhbMasterTransaction::do_compare (uvm_object rhs, uvm_comparer comparer);
  AhbMasterTransaction ahbMasterTransaction;

 if(!$cast(ahbMasterTransaction,rhs)) begin
  `uvm_fatal("FATAL_AHB_MASTER_TX_DO_COMPARE_FAILED","cast of the rhs object failed")
    return 0;
  end

 return super.do_compare(ahbMasterTransaction, comparer) &&
haddr    == ahbMasterTransaction.haddr    &&
hselx    == ahbMasterTransaction.hselx    &&
hburst   == ahbMasterTransaction.hburst   &&
hmastlock == ahbMasterTransaction.hmastlock &&
hprot    == ahbMasterTransaction.hprot    &&
hsize    == ahbMasterTransaction.hsize    &&
hnonsec  == ahbMasterTransaction.hnonsec  &&
hexcl    == ahbMasterTransaction.hexcl    &&
hmaster  == ahbMasterTransaction.hmaster  &&
htrans   == ahbMasterTransaction.htrans   &&
hwdata   == ahbMasterTransaction.hwdata   &&
hwstrb   == ahbMasterTransaction.hwstrb   &&
hwrite   == ahbMasterTransaction.hwrite   &&
hrdata   == ahbMasterTransaction.hrdata   &&
hreadyout == ahbMasterTransaction.hreadyout &&
hresp    == ahbMasterTransaction.hresp    &&
//hexokay  == ahbMasterTransaction.hexokay  &&
hready   == ahbMasterTransaction.hready;

endfunction : do_compare
//--------------------------------------------------------------------------------------------
// Function: do_print method
//  Print method can be added to display the data members values
//
// Parameters:
//  printer - uvm_printer
//--------------------------------------------------------------------------------------------
function void AhbMasterTransaction::do_print(uvm_printer printer);
  
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
printer.print_field  ("hwdata", hwdata, $bits(hwdata), UVM_HEX);
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
// Selects the address based on the slave selected
//--------------------------------------------------------------------------------------------
function void AhbMasterTransaction::post_randomize();
  //Logic
endfunction : post_randomize

`endif
