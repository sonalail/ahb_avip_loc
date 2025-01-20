 
`ifndef AHB_GLOBAL_PKG_INCLUDED_
`define AHB_GLOBAL_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package : AhbGlobalPackage
//  Used for storing required enums, parameters, and defines for AHB interface
//--------------------------------------------------------------------------------------------
package AhbGlobalPackage;

  //------------------------------------------------------------------------------------------
  // Parameters
  //------------------------------------------------------------------------------------------

//Parameter : NO_OF_SLAVES
  //Used to set number of slaves required
  parameter int NO_OF_SLAVES = 1;

  //Parameter : MASTER_AGENT_ACTIVE
  //Used to set the master agent either active or passive
  parameter bit MASTER_AGENT_ACTIVE = 1;

  //Parameter : SLAVE_AGENT_ACTIVE
  //Used to set the slave agent either active or passive
  parameter bit SLAVE_AGENT_ACTIVE = 1;

  // Parameter: ADDR_WIDTH
  // Specifies the width of the address bus
  parameter int ADDR_WIDTH = 32;

  // Parameter: DATA_WIDTH
  // Specifies the width of the data bus
  parameter int DATA_WIDTH = 32;

  // Parameter: HMASTER_WIDTH
  // Specifies the width of the master identifier
  parameter int HMASTER_WIDTH = 4;

  // Parameter: HPROT_WIDTH
  // Specifies the width of the protection control signal
  parameter int HPROT_WIDTH = 4;

  //------------------------------------------------------------------------------------------
  // Enums
  //------------------------------------------------------------------------------------------

  //-------------------------------------------------------
  // Enum: ahb_burst_e
  //  Specifies the burst type of the transfer
  //-------------------------------------------------------
  typedef enum logic [2:0] {
    SINGLE      = 3'b000,
    INCR        = 3'b001,
    WRAP4       = 3'b010,
    INCR4       = 3'b011,
    WRAP8       = 3'b100,
    INCR8       = 3'b101,
    WRAP16      = 3'b110,
    INCR16      = 3'b111
  } ahb_burst_e;

  //-------------------------------------------------------
  // Enum: ahb_transfer_e
  //  Specifies the type of AHB transfer
  //-------------------------------------------------------
  typedef enum logic [1:0] {
    IDLE      = 2'b00,
    BUSY      = 2'b01,
    NONSEQ    = 2'b10,
    SEQ       = 2'b11
  } ahb_transfer_e;

  //-------------------------------------------------------
  // Enum: ahb_resp_e
  //  Specifies the response status
  //-------------------------------------------------------
  typedef enum logic {
    OKAY   = 1'b0,
    ERROR  = 1'b1
  } ahb_resp_e;

  //-------------------------------------------------------
  // Enum: ahb_protection_e
  //  Specifies the type of protection for a transfer
  //-------------------------------------------------------
  typedef enum logic [HPROT_WIDTH-1:0] {
    NORMAL_SECURE_DATA              = 4'b0000,
    NORMAL_SECURE_INSTRUCTION       = 4'b0001,
    NORMAL_NONSECURE_DATA           = 4'b0010,
    NORMAL_NONSECURE_INSTRUCTION    = 4'b0011,
    PRIVILEGED_SECURE_DATA          = 4'b0100,
    PRIVILEGED_SECURE_INSTRUCTION   = 4'b0101,
    PRIVILEGED_NONSECURE_DATA       = 4'b0110,
    PRIVILEGED_NONSECURE_INSTRUCTION = 4'b0111
  } ahb_protection_e;

  //-------------------------------------------------------
  // Struct: ahb_transfer_char_s
  //  This struct datatype includes all key transfer characteristics
  //-------------------------------------------------------
  typedef struct {
    logic [ADDR_WIDTH-1:0] HADDR;          // Address of the transfer
    ahb_burst_e            HBURST;         // Burst type
    logic                  HMASTLOCK;      // Locked sequence indicator
    ahb_protection_e       HPROT;          // Protection type
    logic [2:0]            HSIZE;          // Transfer size
    logic                  HNONSEC;        // Secure or non-secure indicator
    logic                  HEXCL;          // Exclusive access sequence
    logic [HMASTER_WIDTH-1:0] HMASTER;     // Master ID
    ahb_transfer_e         HTRANS;         // Transfer type
    logic [DATA_WIDTH-1:0] HWDATA;         // Write data bus
    logic [(DATA_WIDTH/8)-1:0] HWSTRB;     // Write strobes
    logic                  HWRITE;         // Write or read indicator
    logic [DATA_WIDTH-1:0] HRDATA;         // Read data bus
    logic                  HREADYOUT;      // Transfer completion for subordinate
    ahb_resp_e             HRESP;          // Response status
    logic                  HEXOKAY;        // Exclusive OKAY status
    logic                  HREADY;         // Combined transfer completion
  } ahb_transfer_char_s;

   //-------------------------------------------------------
  // Struct : apb_cfg_char_s
  //  This struct datatype consists of all configurations
  //  which are used for seq item conversion
  //-------------------------------------------------------
  typedef struct{
   
    logic [ADDR_WIDTH-1:0] HADDR;          // Address of the transfer
    
  }apb_transfer_cfg_s;

endpackage : AhbGlobalPackage

`endif





