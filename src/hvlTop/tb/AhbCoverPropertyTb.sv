
`ifndef AHBCOVERPROPERTYTB_INCLUDED_
`define AHBCOVERPROPERTYTB_INCLUDED_

import AhbGlobalPackage::*;

import uvm_pkg::*;
`include "uvm_macros.svh"

module AhbCoverPropertyTb;

 //-------------------------------------------------------
  // Testbench Signals
  //-------------------------------------------------------
  reg         hclk;
  reg         hresetn;
  reg [ADDR_WIDTH-1:0]  haddr;
  reg [DATA_WIDTH-1:0]  hwdata;
  reg [2:0]   hsize;
  reg [2:0]   hburst;
  reg [1:0]   htrans;
  reg         hwrite;
  reg         hready;
  reg         hresp;
  reg         hexcl;
  reg [HPROT_WIDTH-1:0]   hprot;
  reg [HMASTER_WIDTH-1:0]   hmaster;
  reg         hmastlock;
  reg         htransValid;
  reg hreadyout;
  reg[DATA_WIDTH-1:0] hrdata;
 reg [NO_OF_SLAVES-1:0] hselx;
  reg hexokay;
  reg[(DATA_WIDTH/8)-1:0] hwstrb ; 
  reg [DATA_WIDTH-1:0]  hwdataValid;
  string name = "AhbCoverPropertyTb";

 AhbCoverProperty ahbcoverproperty_u(
  .hclk(hclk),
  .hresetn(hresetn),
  .haddr(haddr), 
  .hselx(hselx),
  .hburst(hburst),
  .hmastlock(hmastlock),
  .hprot(hprot),
  .hsize(hsize),
  .hnonsec(hnonsec),
  .hexcl(hexcl),
  .hmaster(hmaster),
  .htrans(htrans),
  .hwdata(hwdata),
  .hwstrb(hwstrb),
  .hwrite(hwrite),
  .hrdata(hrdata),
  .hreadyout(hreadyout),
  .hresp(hresp),
  .hexokay(hexokay),
  .hready(hready)
                           );
//-------------------------------------------------------
// Clock Generation
//-------------------------------------------------------
always begin
  #5 hclk = ~hclk;
end

//-------------------------------------------------------
// Reset Generation
//-------------------------------------------------------
initial begin
  hclk = 0;
  hresetn = 0;
  #15 hresetn = 1;
end

initial begin
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInNonSeqState();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInNonSeqState();
  
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrementBurst();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrementBurst();
  
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap4Burst();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap4Burst();
  
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement4Burst();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement4Burst();
  
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap8Burst();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap8Burst();
  
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement8Burst();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement8Burst();
  
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap16Burst();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap16Burst();
  
  writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement16Burst();
  writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement16Burst();
  
  $finish;
end

//NON - SEQ

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInNonSeqState();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Non-Seq State task Started"),UVM_NONE);
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b10; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b000; // Single transfer
    hsize   = 3'b010; // Word transfer

    // **READ TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b10; // NONSEQ
    haddr   = 32'h1000_1004; // Same address as write
    hburst  = 3'b000; // Single transfer
    hsize   = 3'b010; // Word transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;
 
    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Non-Seq State task ended"),UVM_NONE);
  
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInNonSeqState();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Non-Seq State task Started"),UVM_NONE);

    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    // Cycle 1: Perform Write Transaction
    @(posedge hclk);
    hwrite  = 1;
    htrans  = 2'b10;  // NONSEQ transaction
    haddr   = 32'h1000;  // Initial Address
    hwdata  = 32'hA5A5A5A5;  // Write data
    hready  = 1;
    hresp   = 0; // No error

    // Cycle 2: Perform Read Transaction at a Different Address
    @(posedge hclk);
    hwrite  = 0;
    htrans  = 2'b10;  // NONSEQ transaction
    haddr   = 32'h2000;  // Different Address
    hready  = 1;
    hresp   = 0; // No error
    hrdata  = 32'hA5A5A5A5; // Read data should match written data

    @(posedge hclk);
    @(posedge hclk);

   `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Non-Seq State task ended"),UVM_NONE);
endtask

//SEQ 
//INCREMENT BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrementBurst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment Burst task Started"),UVM_NONE);

    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b11; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b001; // Single transfer
    hsize   = 3'b001; // Word transfer

    // **READ TRANSACTION** (SEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b11; // SEQ
    haddr   = 32'h1000_1005; // Same address as write
    hburst  = 3'b001; // Increment transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment Burst task ended"),UVM_NONE);
endtask


task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrementBurst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment Burst task Started"),UVM_NONE);
   
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // Cycle 1: First Write Transaction (NONSEQ)
    @(posedge hclk);
    hwrite  = 1;
    htrans  = 2'b10;  // NONSEQ transaction
    hburst  = 3'b001; // Incrementing burst
    haddr   = 32'h1000_0000;  // Initial Address
    hwdata  = 32'hA5A5A5A5;  // Write data
    hready  = 1;
    hresp   = 0; // No error

    // Cycle 2: Sequential Write Transaction
    @(posedge hclk);
    hwrite  = 1;
    htrans  = 2'b11;  // SEQ transaction
    hburst  = 3'b001; // Incrementing burst
    haddr   = 32'h1000_0005;  // Different Address (not addr+1)
    hwdata  = 32'h5A5A5A5A;  // Write data
    hready  = 1;
    hresp   = 0;

    @(posedge hclk);
    hwrite  = 0;
    htrans  = 2'b11;  // SEQ transaction
    hburst  = 3'b001; // Incrementing burst
    haddr   = 32'h1000_0000;  // Different Address (not addr+1)
    hrdata  = 32'h5A5A5A5A;  // Write data
    hready  = 1;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment Burst task ended"),UVM_NONE);
endtask

//WRAP4 BURST
task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap4Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap4 Burst task Started"),UVM_NONE);

    // Reset Phase
    @(posedge hclk);
    hburst = 3'b010;  // Wrap-16 burst
    htrans = 2'b11;   // SEQ transaction type
    hready = 1;
    haddr = 32'h10000000; // Initial address
    hwdata = 32'hA5A5A5A5;  // Data for write
    hrdata = 32'hZZZZZZZZ;  // Data for read (initially unknown)
    hwrite = 1;      // Write operation initially enabled

    // Cycle 1 (Write)
    @(posedge hclk) haddr = 32'h10000004; // Start address
    hwdata = 32'hA5A5A5A5; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 2 (Write)
    @(posedge hclk) haddr = 32'h10000008; // Address + 4
    hwdata = 32'h5A5A5A5A; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 3 (Write)
    @(posedge hclk) haddr = 32'h1000000C; // Address + 8
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 4 (Write)
    // Cycle after wrap (Read)
    @(posedge hclk) haddr = 32'h10000000; // Read the initial address
    hwrite = 0;  // Disable write for read
    hrdata = 32'hA5A5A5A5; // Expecting the same data written in the previous cycle
   
    @(posedge hclk);  // Wait for next cycle
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap4 Burst task ended"),UVM_NONE);
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap4Burst();
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap4 Burst task Started"),UVM_NONE);

    // Reset Phase
    @(posedge hclk);
    hburst = 3'b010;  // Wrap-16 burst
    htrans = 2'b11;   // SEQ transaction type
    hready = 1;
    haddr = 32'h10000000; // Initial address
    hwdata = 32'hA5A5A5A5;  // Data for write
    hrdata = 32'hZZZZZZZZ;  // Data for read (initially unknown)
    hwrite = 1;      // Write operation initially enabled

    // Cycle 1 (Write)
    @(posedge hclk) haddr = 32'h10000004; // Start address
    hwdata = 32'hA5A5A5A5; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 2 (Write)
    @(posedge hclk) haddr = 32'h10000008; // Address + 4
    hwdata = 32'h5A5A5A5A; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 3 (Write)
    @(posedge hclk) haddr = 32'h1000000C; // Address + 8
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 4 (Write)
    // Cycle after wrap (Read)
    @(posedge hclk) haddr = 32'h00000000; // Read the initial address
    hwrite = 0;  // Disable write for read
    hrdata = 32'hA5A5A5A5; // Expecting the same data written in the previous cycle
   
    @(posedge hclk);  // Wait for next cycle
    @(posedge hclk);

`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap4 Burst task ended"),UVM_NONE);
endtask

//INCREMENT4 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement4Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment4 Burst task Started"),UVM_NONE);
 
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b10; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b011; // Single transfer
    hsize   = 3'b001; // Word transfer

    // **READ TRANSACTION** (SEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b11; // SEQ
    haddr   = 32'h1000_1008; // Same address as write
    hburst  = 3'b011; // Increment transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment4 Burst task ended"),UVM_NONE);
endtask

  
task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement4Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment4 Burst task Started"),UVM_NONE);
  
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b10; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b011; // Single transfer
    hsize   = 3'b001; // Word transfer

    // **READ TRANSACTION** (SEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b11; // SEQ
    haddr   = 32'h1000_1004; // Same address as write
    hburst  = 3'b011; // Increment transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment4 Burst task ended"),UVM_NONE);
endtask

//WRAP8 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap8Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap8 Burst task Started"),UVM_NONE);
    
    // Reset Phase
    @(posedge hclk);
    hburst = 3'b100;  // Wrap-16 burst
    htrans = 2'b11;   // SEQ transaction type
    hready = 1;
    haddr = 32'h10000000; // Initial address
    hwdata = 32'hA5A5A5A5;  // Data for write
    hrdata = 32'hZZZZZZZZ;  // Data for read (initially unknown)
    hwrite = 1;      // Write operation initially enabled

    // Cycle 1 (Write)
    @(posedge hclk) haddr = 32'h10000004; // Start address
    hwdata = 32'hA5A5A5A5; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 2 (Write)
    @(posedge hclk) haddr = 32'h10000008; // Address + 4
    hwdata = 32'h5A5A5A5A; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 3 (Write)
    @(posedge hclk) haddr = 32'h1000000C; // Address + 8
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 4 (Write)
    @(posedge hclk) haddr = 32'h10000010; // Address + 12
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 5 (Write)
    @(posedge hclk) haddr = 32'h10000014; // Address + 16
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 6 (Write)
    @(posedge hclk) haddr = 32'h10000018; // Address + 20
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 7 (Write)
    @(posedge hclk) haddr = 32'h1000001C; // Address + 24
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 8 (Write)
    // Cycle after wrap (Read)
    @(posedge hclk) haddr = 32'h10000000; // Read the initial address
    hwrite = 0;  // Disable write for read
    hrdata = 32'hA5A5A5A5; // Expecting the same data written in the previous cycle
    @(posedge hclk);  // Wait for next cycle
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap8 Burst task ended"),UVM_NONE);
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap8Burst();
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap8 Burst task Started"),UVM_NONE);
    
    // Reset Phase
    @(posedge hclk);
    hburst = 3'b100;  // Wrap-16 burst
    htrans = 2'b11;   // SEQ transaction type
    hready = 1;
    haddr = 32'h10000000; // Initial address
    hwdata = 32'hA5A5A5A5;  // Data for write
    hrdata = 32'hZZZZZZZZ;  // Data for read (initially unknown)
    hwrite = 1;      // Write operation initially enabled

    // Cycle 1 (Write)
    @(posedge hclk) haddr = 32'h10000004; // Start address
    hwdata = 32'hA5A5A5A5; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 2 (Write)
    @(posedge hclk) haddr = 32'h10000008; // Address + 4
    hwdata = 32'h5A5A5A5A; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 3 (Write)
    @(posedge hclk) haddr = 32'h1000000C; // Address + 8
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 4 (Write)
    @(posedge hclk) haddr = 32'h10000010; // Address + 12
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 5 (Write)
    @(posedge hclk) haddr = 32'h10000014; // Address + 16
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 6 (Write)
    @(posedge hclk) haddr = 32'h10000018; // Address + 20
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 7 (Write)
    @(posedge hclk) haddr = 32'h1000001C; // Address + 24
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 8 (Write)
    // Cycle after wrap (Read)
    @(posedge hclk) haddr = 32'h00000000; // Read the initial address
    hwrite = 0;  // Disable write for read
    hrdata = 32'hA5A5A5A5; // Expecting the same data written in the previous cycle
    @(posedge hclk);  // Wait for next cycle
    @(posedge hclk);

`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap8 Burst task ended"),UVM_NONE);
endtask

//INCRMENT 8

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement8Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment8 Burst task Started"),UVM_NONE);
 
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b10; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b101; // Single transfer
    hsize   = 3'b001; // Word transfer

    // **READ TRANSACTION** (SEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b11; // SEQ
    haddr   = 32'h1000_100C; // Same address as write
    hburst  = 3'b011; // Increment transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment8 Burst task ended"),UVM_NONE);
endtask

  
task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement8Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment8 Burst task Started"),UVM_NONE);
 
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b10; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b101; // Single transfer
    hsize   = 3'b001; // Word transfer

    // **READ TRANSACTION** (SEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b11; // SEQ
    haddr   = 32'h1000_1000; // Same address as write
    hburst  = 3'b011; // Increment transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment8 Burst task ended"),UVM_NONE);
endtask


//WRAP16 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap16Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap16 Burst task Started"),UVM_NONE);

    // Reset Phase
    @(posedge hclk);
    hburst = 3'b110;  // Wrap-16 burst
    htrans = 2'b11;   // SEQ transaction type
    hready = 1;
    haddr = 32'h10000000; // Initial address
    hwdata = 32'hA5A5A5A5;  // Data for write
    hrdata = 32'hZZZZZZZZ;  // Data for read (initially unknown)
    hwrite = 1;      // Write operation initially enabled

    // Cycle 1 (Write)
    @(posedge hclk) haddr = 32'h10000004; // Start address
    hwdata = 32'hA5A5A5A5; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 2 (Write)
    @(posedge hclk) haddr = 32'h10000008; // Address + 4
    hwdata = 32'h5A5A5A5A; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 3 (Write)
    @(posedge hclk) haddr = 32'h1000000C; // Address + 8
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 4 (Write)
    @(posedge hclk) haddr = 32'h10000010; // Address + 12
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 5 (Write)
    @(posedge hclk) haddr = 32'h10000014; // Address + 16
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 6 (Write)
    @(posedge hclk) haddr = 32'h10000018; // Address + 20
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 7 (Write)
    @(posedge hclk) haddr = 32'h1000001C; // Address + 24
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 8 (Write)
    @(posedge hclk) haddr = 32'h10000020; // Address + 28
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 9 (Write)
    @(posedge hclk) haddr = 32'h10000024; // Address + 32
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 10 (Write)
    @(posedge hclk) haddr = 32'h10000028; // Address + 36
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 11 (Write)
    @(posedge hclk) haddr = 32'h1000002C; // Address + 40
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 12 (Write)
    @(posedge hclk) haddr = 32'h10000030; // Address + 44
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 13 (Write)
    @(posedge hclk) haddr = 32'h10000034; // Address + 48
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 14 (Write)
    @(posedge hclk) haddr = 32'h10000038; // Address + 52
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 15 (Write)
    @(posedge hclk) haddr = 32'h1000003C; // Address + 56
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 16 (Write)
    // Cycle after wrap (Read)
    @(posedge hclk) haddr = 32'h10000000; // Read the initial address
    hwrite = 0;  // Disable write for read
    hrdata = 32'hA5A5A5A5; // Expecting the same data written in the previous cycle
    @(posedge hclk);  // Wait for next cycle
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap16 Burst task ended"),UVM_NONE);
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap16Burst();
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap16 Burst task Started"),UVM_NONE);

    // Reset Phase
    @(posedge hclk);
    hburst = 3'b110;  // Wrap-16 burst
    htrans = 2'b11;   // SEQ transaction type
    hready = 1;
    haddr = 32'h10000000; // Initial address
    hwdata = 32'hA5A5A5A5;  // Data for write
    hrdata = 32'hZZZZZZZZ;  // Data for read (initially unknown)
    hwrite = 1;      // Write operation initially enabled

    // Cycle 1 (Write)
    @(posedge hclk) haddr = 32'h10000004; // Start address
    hwdata = 32'hA5A5A5A5; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 2 (Write)
    @(posedge hclk) haddr = 32'h10000008; // Address + 4
    hwdata = 32'h5A5A5A5A; // Data for write
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 3 (Write)
    @(posedge hclk) haddr = 32'h1000000C; // Address + 8
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 4 (Write)
    @(posedge hclk) haddr = 32'h10000010; // Address + 12
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 5 (Write)
    @(posedge hclk) haddr = 32'h10000014; // Address + 16
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 6 (Write)
    @(posedge hclk) haddr = 32'h10000018; // Address + 20
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 7 (Write)
    @(posedge hclk) haddr = 32'h1000001C; // Address + 24
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 8 (Write)
    @(posedge hclk) haddr = 32'h10000020; // Address + 28
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 9 (Write)
    @(posedge hclk) haddr = 32'h10000024; // Address + 32
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 10 (Write)
    @(posedge hclk) haddr = 32'h10000028; // Address + 36
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 11 (Write)
    @(posedge hclk) haddr = 32'h1000002C; // Address + 40
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 12 (Write)
    @(posedge hclk) haddr = 32'h10000030; // Address + 44
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 13 (Write)
    @(posedge hclk) haddr = 32'h10000034; // Address + 48
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 14 (Write)
    @(posedge hclk) haddr = 32'h10000038; // Address + 52
    hwdata = 32'h5A5A5A5A; // Same data as Cycle 2
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 15 (Write)
    @(posedge hclk) haddr = 32'h1000003C; // Address + 56
    hwdata = 32'hA5A5A5A5; // Same data as Cycle 1
    hwrite = 1;  // Enable write
    htrans = 2'b11;  // SEQ transaction

    // Cycle 16 (Write)
    // Cycle after wrap (Read)
    @(posedge hclk) haddr = 32'h00000000; // Read the initial address
    hwrite = 0;  // Disable write for read
    hrdata = 32'hA5A5A5A5; // Expecting the same data written in the previous cycle
    @(posedge hclk);  // Wait for next cycle
    @(posedge hclk);

`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap16 Burst task ended"),UVM_NONE);
endtask

//INCREMENT16 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement16Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment16 Burst task Started"),UVM_NONE);
 
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b10; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b111; // Single transfer
    hsize   = 3'b001; // Word transfer

    // **READ TRANSACTION** (SEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b11; // SEQ
    haddr   = 32'h1000_1014; // Same address as write
    hburst  = 3'b011; // Increment transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment16 Burst task ended"),UVM_NONE);
endtask

  
task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement16Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment16 Burst task Started"),UVM_NONE);
 
    // Reset Phase
    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; // IDLE
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; // Word transfer
    hburst  = 3'b000; // Single transfer
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; // Ready for transactions

    // **WRITE TRANSACTION** (NONSEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; // Write Operation
    htrans  = 2'b10; // NONSEQ (Start of a new transaction)
    haddr   = 32'h1000_1004; // Address
    hwdata  = 32'h1234_abcd; // Data
    hburst  = 3'b111; // Single transfer
    hsize   = 3'b001; // Word transfer

    // **READ TRANSACTION** (SEQ)
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; // Read Operation
    htrans  = 2'b11; // SEQ
    haddr   = 32'h1000_1000; // Same address as write
    hburst  = 3'b011; // Increment transfer
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment16 Burst task ended"),UVM_NONE);
endtask

 initial begin
   $monitor("Time=%0t, htrans=%b, hresp=%b, hreadyout=%b, hsize = %b , hwdata =%h, hrdata=%h, haddr=%h, hwrite=%b, hburst=%b",
             $time, htrans, hresp, hreadyout,hsize, hwdata, hrdata, haddr, hwrite, hburst);
  end

endmodule
`endif




