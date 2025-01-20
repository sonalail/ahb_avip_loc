`ifndef AHB_IF_INCLUDED_
`define AHB_IF_INCLUDED_

// Importing ahb global package (if applicable)
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Declaration of pin level signals for AHB interface
//--------------------------------------------------------------------------------------------

interface ahb_if(input HCLK, input HRESETn);
  
  // Variable : HADDR
  // Byte address of the transfer
  logic [ADDR_WIDTH-1:0] HADDR;

  // Variable : HBURST
  // Indicates burst type
  logic [2:0] HBURST;

  // Variable : HMASTLOCK
  // Indicates a locked sequence
  logic HMASTLOCK;

  // Variable : HPROT
  // Protection control signal
  logic [HPROT_WIDTH-1:0] HPROT;

  // Variable : HSIZE
  // Indicates the size of a transfer
  logic [2:0] HSIZE;

  // Variable : HNONSEC
  // Indicates whether the transfer is Non-secure or Secure
  logic HNONSEC;

  // Variable : HEXCL
  // Indicates Exclusive Access sequence
  logic HEXCL;

  // Variable : HMASTER
  // Manager identifier
  logic [HMASTER_WIDTH-1:0] HMASTER;

  // Variable : HTRANS
  // Indicates the transfer type
  logic [1:0] HTRANS;

  // Variable : HWDATA
  // Write data bus
  logic [DATA_WIDTH-1:0] HWDATA;

  // Variable : HWSTRB
  // Write strobes for active byte lanes
  logic [(DATA_WIDTH/8)-1:0] HWSTRB;

  // Variable : HWRITE
  // Indicates transfer direction (1 = write, 0 = read)
  logic HWRITE;

  // Variable : HRDATA
  // Read data bus
  logic [DATA_WIDTH-1:0] HRDATA;

  // Variable : HREADYOUT
  // Indicates transfer completion for a Subordinate
  logic HREADYOUT;

  // Variable : HRESP
  // Transfer response status (0 = OKAY, 1 = ERROR)
  logic HRESP;

  // Variable : HEXOKAY
  // Indicates Exclusive OKAY status
  logic HEXOKAY;

  // Variable : HREADY
  // Combined transfer completion for Manager and Subordinate
  logic HREADY;

endinterface : ahb_if

`endif

