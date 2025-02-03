// Code your design here
// Code your testbench here
// or browse Examples
`ifndef AHBMASTERASSERTIONTB_INCLUDED_
`define AHBMASTERASSERTIONTB_INCLUDED_

import AhbGlobalPackage::*;

import uvm_pkg::*;
`include "uvm_macros.svh"

module AhbMasterAssertionTb;

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
  reg [DATA_WIDTH-1:0]  hwdataValid;
  string name = "AhbMasterAssertionTb";

  //-------------------------------------------------------
  // Instantiate the Assertions Interface
  //-------------------------------------------------------
  AhbMasterAssertion ahbmasterassertions_u (
    .hclk(hclk),
    .hresetn(hresetn),
    .haddr(haddr),
    .hwdata(hwdata),
    .hsize(hsize),
    .hburst(hburst),
    .htrans(htrans),
    .hwrite(hwrite),
    .hready(hready),
    .hresp(hresp),
    .hexcl(hexcl),
    .hprot(hprot),
    .hmaster(hmaster),
    .hmastlock(hmastlock),
    .htransValid(htransValid),
    .hwdataValid(hwdataValid)
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
  //calling tasks
  initial begin
    Initialize();
    CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionPass();
    CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionFail(); 
    
    EnsureHADDRIsAlignedBasedOnHSIZEAssertionFail(); 
    EnsureHADDRIsAlignedBasedOnHSIZEAssertionPass(); 
    
    CheckIfHADDRIsWithinTheValidRrangeAssertionPass();
    CheckIfHADDRIsWithinTheValidRrangeAssertionFail();
    
    EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionPass();
    EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionFail();
    EnsureHRESPIsERRORDuringSuccessfulTransfersAssertionPass();
    
    CheckForINCRAssertionPass();
    CheckForINCRAssertionFail();
    
    EnsureHREADYRemainsStableDuringWaitStatesAssertionPass();
    EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionPass();
    EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionFail();
    
    CheckForWRAPAssertionPass();
    CheckForWRAPAssertionFail();
      $finish;
    
  end
    

  //-------------------------------------------------------
  // Stimulus Generation
  //-------------------------------------------------------

    task Initialize();     
      `uvm_info(name,$sformatf("Initializing signals started"),UVM_NONE);
      @(posedge hclk)
    haddr = 32'h00000000;
    hwdata = 32'h12345678;
    hsize = 3'b010;  // Word (32-bit)
    hburst = 3'b001; // INCR burst type
    htrans = 2'b10;  // Non-sequential transfer
    hwrite = 1;
    hready = 1;
    hresp = 1'b0;    // OKAY response
    hexcl = 0;
    hprot = 4'b0000;
    hmaster = 4'b0001;
    hmastlock = 0;
    htransValid = 1;
    hwdataValid = 1;
      `uvm_info(name,$sformatf("Initializing signals ended"),UVM_NONE);
    endtask

    // Stimulus 1: **Valid Write Transaction** (Passing Test for Assertions)
    task CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionPass();     
      `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionPass Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00000004;
      hwdata = 32'h87654321;
      hsize = 3'b010;  // 32-bit transfer
      htrans = 2'b11;  // Sequential transfer
      hwrite = 1;
      hready = 1;
      #20;                                                  
     `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionPass Task ended"),UVM_NONE);   
   endtask

    //Stimulus 1.1: **Invalid Write Transaction** (Fail Test for Assertions)
    task CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionFail(); 
      `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionFail Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00000004;
      hwdata =32'hx;
      hsize = 3'b010;
      htrans = 2'b11;
      hwrite = 1;
      hready = 1;
      #20;
     `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionFail Task ended"),UVM_NONE);
    endtask

     // Stimulus 2: **Invalid HADDR Alignment** (Failing the HADDR Alignment Assertion
     task EnsureHADDRIsAlignedBasedOnHSIZEAssertionFail();   
       `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionFail task started"),UVM_NONE);
        @(posedge hclk);
        haddr = 32'h00000003; // Misaligned address (not divisible by 4 for 32-bit transfer)
        hwdata = 32'hDEADBEEF;
        hwrite = 1;
        hready = 1;
        htrans = 2'b10;  // Non-sequential transfer
        #20;
       `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionFail Task ended"),UVM_NONE);
       
     endtask
    

    //Stimulus 2.1: **Valid HADDR Alignment** (Passing Assertion)
    task EnsureHADDRIsAlignedBasedOnHSIZEAssertionPass();   
      `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionPass task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'h10000000;
       hsize = 3'b010;
       hready = 1;
       htrans = 2'b11;
       hwrite = 1;
       hready = 1;
       #20;
      `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionPass Task ended"),UVM_NONE);    
    endtask
      
    // Stimulus 3: **Valid HADDR within range**
    task CheckIfHADDRIsWithinTheValidRrangeAssertionPass();
      `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionPass Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h10000000;  // Valid address in the range
      hsize = 3'b010;        // 32-bit transfer
      htrans = 2'b11;        // Sequential transfer
      hwrite = 1;
      hready = 1;
      #20;
      `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionPass Task ended"),UVM_NONE);
    endtask

    // Stimulus 4: **HADDR out of range** (Failing the Address Range Assertion)
     task CheckIfHADDRIsWithinTheValidRrangeAssertionFail();
       `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionFail Task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'hFFFFFFFFF; // Invalid address out of range
       hwdata = 32'hC0FFEE;
       hsize = 3'b010;        // 32-bit transfer
       htrans = 2'b10;        // Non-sequential transfer
       hwrite = 1;
       hready = 1;
       #20;
       `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionFail Task ended"),UVM_NONE);
     endtask
    

    // Stimulus 5: **Valid HRESP** (Passing Test for HRESP OKAY Assertion)
    task EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionPass();
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionPass Task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'h00000008;
       hwdata = 32'hABCDEF01;
       hresp = 1'b0;   // OKAY response
       htrans = 2'b11; // Sequential transfer
       hready = 1;
       hwrite = 1;
       #20;
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionPass Task ended"),UVM_NONE);
    endtask

    // Stimulus 6: **Invalid HRESP** (Failing the HRESP Error Assertion)
    task EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionFail();
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionFail Task started"),UVM_NONE);
       @(posedge hclk);
       hresp = 1'b1; // ERROR response
       hready = 1;
       hwrite = 1;
       htrans = 2'b11; // Sequential transfer
       #20;
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionFail Task ended"),UVM_NONE);
    endtask

    //Stimuls 6.1 : **HRESP is ERROR**(Failing Assertion)
    task EnsureHRESPIsERRORDuringSuccessfulTransfersAssertionPass();
      `uvm_info(name,$sformatf("Ensure HRESP is ERROR (1) during successful transfers AssertionPass Task started"),UVM_NONE);
       @(posedge hclk);
       hready = 1;
       hresp = 1;
       htrans = 2'b00;
       hwrite = 1;
       #20;
      `uvm_info(name,$sformatf("Ensure HRESP is ERROR (1) during successful transfers AssertionPass Task ended"),UVM_NONE);
    endtask


    // Stimulus 7: **Burst Transfer (INCR)**
    task CheckForINCRAssertionPass();
     `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionPass Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00000000;
      hburst = 3'b001; // INCR burst
      hsize = 3'b001;  // 8-bit transfer
      htrans = 2'b11;  // Sequential transfer
      hwrite = 1;
      hready = 1;
      #20;
      `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionPass Task ended"),UVM_NONE);
    endtask
    
     // Stimulus 7.1: **Invalid INCR Burst Address**
    task CheckForINCRAssertionFail();
      `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionFail Task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'h00000001;  // Invalid address for INCR burst type
       hburst = 3'b001;       // INCR burst type
       hsize = 3'b001;        // 8-bit transfer
       htrans = 2'b11;        // Sequential transfer
       hwrite = 1;
       hready = 1;
       #20;
      `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionFail Task ended"),UVM_NONE);
    endtask

//     // Stimulus 8: **Burst Transfer (WRAP)**
//     #10;
//     haddr = 32'h00000000;
//     hburst = 3'b010; // WRAP burst
//     hsize = 3'b010;  // 16-bit transfer
//     htrans = 2'b11;  // Sequential transfer
//     hwrite = 1;
//     hready = 1;
//     #20;

    // Stimulus 9: **HREADY Stability Test** (Passing HREADY Stability Test)
    task EnsureHREADYRemainsStableDuringWaitStatesAssertionPass();
      `uvm_info(name,$sformatf("Ensure HREADY remains stable during wait states Assertion Pass Task started"),UVM_NONE);
       @(posedge hclk);
       hready = 0; // Simulating slave not ready
       #10;
       hready = 1; // HREADY must stay stable until slave is ready
       #20;
      `uvm_info(name,$sformatf("Ensure HREADY remains stable during wait states Assertion Pass Task ended"),UVM_NONE);

    // Stimulus 10: **HMASTLOCK** (Valid locked transfer)
      task EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionPass();
        `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Pass Task started"),UVM_NONE);
        @(posedge hclk);
        hmastlock = 1;  // Assert HMASTLOCK during a transfer
        haddr = 32'h00000010;
        htrans = 2'b11; // Sequential transfer
        hwrite = 1;
        hready = 1;
        #20;
        `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Pass Task ended"),UVM_NONE);
      endtask

    //Stimulus 10.1: **HMASTLOCK** (Invalid)
      task EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionFail();
       `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Fail Task started"),UVM_NONE);
         @(posedge hclk);
        hmastlock = 0;  // Deassert HMASTLOCK during a transfer
        haddr = 32'h00000010;
        htrans = 2'b11; // Sequential transfer
        hwrite = 1;
        hready = 1;
        #10;
        hmastlock = 0;
        #20;
        `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Fail Task ended"),UVM_NONE);
      endtask

   

//     // Stimulus 12: **Valid INCR Burst Address**
//     #10;
//     haddr = 32'h00000000;  // Valid address for INCR burst type
//     hburst = 3'b001;       // INCR burst type
//     hsize = 3'b010;        // 16-bit transfer
//     htrans = 2'b11;        // Sequential transfer
//     hwrite = 1;
//     hready = 1;
//     #20;

    // Stimulus 13: **Burst wrapping error**(pass assertion)
    task CheckForWRAPAssertionPass():
      `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionPass Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00000010; // Address for WRAP burst type, but it doesn't align
      hburst = 3'b010;      // WRAP burst type
      hsize = 3'b001;       // 8-bit transfer
      htrans = 2'b11;       // Sequential transfer
      hwrite = 1;
      hready = 1;
      #20;
      `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionPass Task ended"),UVM_NONE);
    endtask
          

    //Stimulus 13.1 **Burst wrapping fail**
    task CheckForWRAPAssertionFail():
      `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionFail Task started"),UVM_NONE);
      @(posedge hclk);
    #10;
    haddr = 32'h00001111; // Misaligned address
    hburst = 3'b010;      // WRAP burst type
    hsize = 3'b001;       // 8-bit transfer
    htrans = 2'b11;       // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;
    `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionPass Task ended"),UVM_NONE);
    endtask



endmodule
`endif
