`ifndef AHBINTERFACE_INCLUDED_
`define AHBINTERFACE_INCLUDED_

// Importing ahb global package 
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Declaration of pin level signals for AHB interface
//--------------------------------------------------------------------------------------------

interface AhbInterface(input hclk, input hresetn);
  
  // Variable : haddr
  // Byte address of the transfer
  logic [ADDR_WIDTH-1:0] haddr;

  //Variable : hselx
  //Indicates the number of slaves
  logic [NO_OF_SLAVES-1:0] hselx;
  
  // Variable : hburst
  // Indicates burst type
  logic [2:0] hburst;

  // Variable : hmastlock
  // Indicates a locked sequence
  logic hmastlock;

  // Variable : hprot
  // Protection control signal
  logic [HPROT_WIDTH-1:0] hprot;

  // Variable : hsize
  // Indicates the size of a transfer
  logic [2:0] hsize;

  // Variable : hnonsec
  // Indicates whether the transfer is Non-secure or Secure
  logic hnonsec;

  // Variable : hexcl
  // Indicates Exclusive Access sequence
  logic hexcl;

  // Variable : hmaster
  // Manager identifier
  logic [HMASTER_WIDTH-1:0] hmaster;

  // Variable : htrans
  // Indicates the transfer type
  logic [1:0] htrans;

  // Variable : hwdata
  // Write data bus
  logic [DATA_WIDTH-1:0] hwdata;

  // Variable : hwstrb
  // Write strobes for active byte lanes
  logic [(DATA_WIDTH/8)-1:0] hwstrb;

  // Variable : hwrite
  // Indicates transfer direction (1 = write, 0 = read)
  logic hwrite;

  // Variable : hrdata
  // Read data bus
  logic [DATA_WIDTH-1:0] hrdata;

  // Variable : hreadyout
  // Indicates transfer completion for a Subordinate
  logic hreadyout;

  // Variable : hresp
  // Transfer response status (0 = OKAY, 1 = ERROR)
  logic hresp;

  // Variable : hexokay
  // Indicates Exclusive OKAY status
  logic hexokay;

  // Variable : hready
  // Combined transfer completion for Manager and Subordinate
  logic hready;


endinterface : AhbInterface

`endif

