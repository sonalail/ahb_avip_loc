 
`ifndef AHBGLOBALPACKAGE_INCLUDED_
`define AHBGLOBALPACKAGE_INCLUDED_

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
  // Enum: ahbBurstEnum
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
  } ahbBurstEnum;

  //-------------------------------------------------------
  // Enum: ahbTransferEnum
  //  Specifies the type of AHB transfer
  //-------------------------------------------------------
  typedef enum logic [1:0] {
    IDLE      = 2'b00,
    BUSY      = 2'b01,
    NONSEQ    = 2'b10,
    SEQ       = 2'b11
  } ahbTransferEnum;

  //-------------------------------------------------------
  // Enum: ahbRespEnum
  //  Specifies the response status
  //-------------------------------------------------------
  typedef enum logic {
    OKAY   = 1'b0,
    ERROR  = 1'b1
  } ahbRespEnum;

//-------------------------------------------------------
// Enum: ahbHsizeEnum
//  Specifies the size of a data transfer for HSIZE
//-------------------------------------------------------
typedef enum logic [2:0] {
  BYTE        = 3'b000, // 8 bits
  HALFWORD    = 3'b001, // 16 bits
  WORD        = 3'b010, // 32 bits
  DOUBLEWORD  = 3'b011, // 64 bits
  LINE4       = 3'b100, // 128 bits (4-word line)
  LINE8       = 3'b101, // 256 bits (8-word line)
  LINE16      = 3'b110, // 512 bits
  LINE32      = 3'b111  // 1024 bits
} ahbHsizeEnum;

 
  //-------------------------------------------------------
  // Enum: ahbProtectionEnum
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
  } ahbProtectionEnum;

  //-------------------------------------------------------
  // Struct: ahbTransferCharStruct
  //  This struct datatype includes all key transfer characteristics
  //-------------------------------------------------------
typedef struct {
logic [ADDR_WIDTH-1:0]  haddr;          // Address of the transfer
ahbBurstEnum            hburst;         // Burst type
logic                   hmastlock;      // Locked sequence indicator
ahbProtectionEnum       hprot;          // Protection type
ahbHsizeEnum            hsize;          // Transfer size
logic                   hnonsec;        // Secure or non-secure indicator
logic                   hexcl;          // Exclusive access sequence
logic [HMASTER_WIDTH-1:0] hmaster;     // Master ID
ahbTransferEnum          htrans;        // Transfer type
logic [DATA_WIDTH-1:0]   hwdata;         // Write data bus
logic [(DATA_WIDTH/8)-1:0] hwstrb;     // Write strobes
logic                   hwrite;         // Write or read indicator
logic [DATA_WIDTH-1:0]  hrdata;         // Read data bus
logic                   hreadyout;      // Transfer completion for subordinate
ahbRespEnum             hresp;          // Response status
logic                   hexokay;        // Exclusive OKAY status
logic                   hready;         // Combined transfer completion
  } ahbTransferCharStruct;

   //-------------------------------------------------------
  // Struct : ahbTransferConfigStruct 
  //  This struct datatype consists of all configurations
  //  which are used for seq item conversion
  //-------------------------------------------------------
  typedef struct{
   
    logic [ADDR_WIDTH-1:0] haddr;          // Address of the transfer
   // bit [ADDRESS_WIDTH-1:0]min_address;
   // bit [ADDRESS_WIDTH-1:0]max_address; 
   // int slave_id;
  } ahbTransferConfigStruct ;

endpackage : AhbGlobalPackage

`endif





