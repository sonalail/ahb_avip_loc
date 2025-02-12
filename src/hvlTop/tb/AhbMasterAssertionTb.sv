
`ifndef AHBMASTERASSERTIONTB_INCLUDED_
`define AHBMASTERASSERTIONTB_INCLUDED_

import AhbGlobalPackage::*;

import uvm_pkg::*;
`include "uvm_macros.svh"

module AhbMasterAssertionTb;
  reg                     hclk;
  reg                     hresetn;
  reg    [ADDR_WIDTH-1:0] haddr;
  reg    [DATA_WIDTH-1:0] hwdata;
  reg               [2:0] hsize;
  reg               [2:0] hburst;
  reg               [1:0] htrans;
  reg                     hwrite;
  reg                     hready;
  reg                     hresp; 
  reg                     hexcl;
  reg   [HPROT_WIDTH-1:0] hprot;
  reg [HMASTER_WIDTH-1:0] hmaster;
  reg                     hmastlock;
  reg                     htransValid;
  reg    [DATA_WIDTH-1:0] hwdataValid;
  reg                     hselx;
  string name = "AhbMasterAssertionTb";

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
    .hwdataValid(hwdataValid),
    .hselx(hselx)
  );

  always begin
    #5 hclk = ~hclk;
  end
  
  initial begin
    hclk = 0;
    hresetn = 0;
    #15 hresetn = 1;
  end

  initial begin
    Initialize();
    CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionPass();
    CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionFail(); 
    
    EnsureHADDRIsAlignedBasedOnHSIZEAssertionPass(); 
    EnsureHADDRIsAlignedBasedOnHSIZEAssertionFail(); 
     
    CheckIfHADDRIsWithinTheValidRrangeAssertionPass();
    CheckIfHADDRIsWithinTheValidRrangeAssertionFail();
    
    EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionPass();
    EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionFail();
    EnsureHRESPIsERRORDuringSuccessfulTransfersAssertionPass();
    
    CheckForINCRAssertionPass();
    CheckForINCRAssertionFail();
    
    EnsureHREADYRemainsStableDuringWaitStatesAssertionPass();
    EnsureHREADYRemainsStableDuringWaitStatesAssertionFail();
    
    EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionPass();
    EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionFail();
    
    CheckForWRAPAssertionPass();
    CheckForWRAPAssertionFail();
    
    CheckTransBusyToSeqAssertionPass();
    CheckTransBusyToSeqAssertionFail();
   
    CheckTransBusyToNonSeqAssertionPass();
    CheckTransBusyToNonSeqAssertionFail();

    CheckTransIdleToNonSeqAssertionPass();
    CheckTransIdleToNonSeqAssertionFail();
    
    checkAddrStabilityAssertionPass();
    checkAddrStabilityAssertionFail();
    $finish;   
  end    

    task Initialize();     
      `uvm_info(name,$sformatf("Initializing signals when resetn is deasserted started"),UVM_NONE);
      @(posedge hclk)
      if(hresetn==0) 
        begin
        haddr = 32'h00000000;
        hwdata = 32'hxxxx_xxxx;
        hsize = 3'b010; 
        hburst = 3'b001; 
        htrans = 2'b10;  
        hwrite = 1;
        hready = 1;
        hresp = 1'b0; 
        hexcl = 0;
        hprot = 4'b0000;
        hmaster = 4'b0001;
        hmastlock = 0;
        htransValid = 1;
        hwdataValid = 1;
        hselx  = 0;
        end
        `uvm_info(name,$sformatf("Initializing signals ended"),UVM_NONE);
    endtask

    task CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionPass();     
      `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionPass Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00000004;
      hsize = 3'b010;  
      htrans = 2'b11;  
      hwrite = 1;
      hready = 1;
      hselx  = 1;
      @(posedge hclk);
      hwdata = 32'h87654321;
      @(posedge hclk);                                                
     `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionPass Task ended"),UVM_NONE);   
   endtask

    task CheckThatHWDATAIsValidWhenHWRITEIsHIGHAssertionFail(); 
      `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionFail Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00000004;
      hsize = 3'b010;
      htrans = 2'b11;
      hwrite = 1;
      hready = 1;
      hselx  = 1;
      @(posedge hclk);
      hwdata =32'hx;
      @(posedge hclk);
     `uvm_info(name,$sformatf("Check that HWDATA is valid when HWRITE is HIGH AssertionFail Task ended"),UVM_NONE);
    endtask
  
    task EnsureHADDRIsAlignedBasedOnHSIZEAssertionPass();   
      `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionPass task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'h10000000;
       hsize = 3'b010;
       hready = 1;
       htrans = 2'b11;
       hwrite = 1;
       hready = 1;
       @(posedge hclk);
      `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionPass Task ended"),UVM_NONE);    
    endtask
  
     task EnsureHADDRIsAlignedBasedOnHSIZEAssertionFail();   
       `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionFail task started"),UVM_NONE);
        @(posedge hclk);
        haddr = 32'h00000003; 
        hwrite = 1;
        hready = 1;
        htrans = 2'b10; 
        hselx  = 1;
        @(posedge hclk);
        hwdata = 32'hDEADBEEF;
	@(posedge hclk);
       `uvm_info(name,$sformatf("Ensure HADDR is aligned based on HSIZE AssertionFail Task ended"),UVM_NONE);    
     endtask
  
      
    task CheckIfHADDRIsWithinTheValidRrangeAssertionPass();
      `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionPass Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h10000000;  
      hsize = 3'b010;        
      htrans = 2'b11;       
      hwrite = 1;
      hready = 1;
      @(posedge hclk);
      `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionPass Task ended"),UVM_NONE);
    endtask

  
    task CheckIfHADDRIsWithinTheValidRrangeAssertionFail();
      `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionFail Task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'hFFFFFFFF; 
       hsize = 3'b010;       
       htrans = 2'b10;        
       hwrite = 1;
       hready = 1;
       hselx  = 1;
       @(posedge hclk);
       hwdata = 32'hC0FFEE;
       @(posedge hclk);
       `uvm_info(name,$sformatf("Check if HADDR is within the valid range AssertionFail Task ended"),UVM_NONE);
    endtask
    
    task EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionPass();
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionPass Task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'h00000008;
       hresp = 1'b0;
       htrans = 2'b11;
       hready = 1;
       hwrite = 1;
       hselx  = 1;
       @(posedge hclk);
       hwdata = 32'hABCDEF01;
       @(posedge hclk);
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionPass Task ended"),UVM_NONE);
    endtask

    task EnsureHRESPIsOKAYDuringSuccessfulTransfersAssertionFail();
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionFail Task started"),UVM_NONE);
       @(posedge hclk);
       hresp = 1'b1;
       hready = 1;
       hwrite = 1;
       htrans = 2'b11; 
       @(posedge hclk);
      `uvm_info(name,$sformatf("Ensure HRESP is OKAY (0) during successful transfers AssertionFail Task ended"),UVM_NONE);
    endtask

    task EnsureHRESPIsERRORDuringSuccessfulTransfersAssertionPass();
      `uvm_info(name,$sformatf("Ensure HRESP is ERROR (1) during successful transfers AssertionPass Task started"),UVM_NONE);
       @(posedge hclk);
       hready = 1;
       hresp = 1;
       htrans = 2'b00;
       hwrite = 1;
       @(posedge hclk);
      `uvm_info(name,$sformatf("Ensure HRESP is ERROR (1) during successful transfers AssertionPass Task ended"),UVM_NONE);
    endtask
  
    task CheckForINCRAssertionPass();
     `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionPass Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00000000;
      hburst = 3'b001; 
      hsize = 3'b001;  
      htrans = 2'b11;  
      hwrite = 1;
      hready = 1;
      @(posedge hclk);
      `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionPass Task ended"),UVM_NONE);
    endtask
    
    task CheckForINCRAssertionFail();
      `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionFail Task started"),UVM_NONE);
       @(posedge hclk);
       haddr = 32'h00000001;  
       hburst = 3'b001;    
       hsize = 3'b001;        
       htrans = 2'b11;        
       hwrite = 1;
       hready = 1;
       @(posedge hclk);
      `uvm_info(name,$sformatf("Check for INCR (incrementing burst) AssertionFail Task ended"),UVM_NONE);
    endtask

    task EnsureHREADYRemainsStableDuringWaitStatesAssertionPass();
      `uvm_info(name,$sformatf("Ensure HREADY remains stable during wait states Assertion Pass Task started"),UVM_NONE);
       @(posedge hclk);
       hready = 0; 
       @(posedge hclk);
       hready = 1; 
       @(posedge hclk);
      `uvm_info(name,$sformatf("Ensure HREADY remains stable during wait states Assertion Pass Task ended"),UVM_NONE);
    endtask

    task EnsureHREADYRemainsStableDuringWaitStatesAssertionFail();
      `uvm_info(name,$sformatf("Ensure HREADY remains stable during wait states Assertion Fail Task started"),UVM_NONE);
       @(posedge hclk);
       hready = 0;
       @(posedge hclk);
       hready = 0; 
       @(posedge hclk);
      `uvm_info(name,$sformatf("Ensure HREADY remains stable during wait states Assertion Fail Task ended"),UVM_NONE);
    endtask

    task EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionPass();
      `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Pass Task started"),UVM_NONE);
       @(posedge hclk);
       hmastlock = 1;  
       haddr = 32'h00000010;
       htrans = 2'b11; 
       hwrite = 1;
       hready = 1;
       @(posedge hclk);
       `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Pass Task ended"),UVM_NONE);
    endtask

    task EnsureHMASTLOCKIsAssertedCorrectlyDuringLockedTransfersAssertionFail();
       `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Fail Task started"),UVM_NONE);
        @(posedge hclk);
        hmastlock = 0;  
        haddr = 32'h00000010;
        htrans = 2'b11; 
        hwrite = 1;
        hready = 1;
        @(posedge hclk);
        hmastlock = 0;
        @(posedge hclk);
        `uvm_info(name,$sformatf(" Ensure HMASTLOCK is asserted correctly during locked transfers Assertion Fail Task ended"),UVM_NONE);
      endtask
  
      task CheckForWRAPAssertionPass();
        `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionPass Task started"),UVM_NONE);
        @(posedge hclk);
        haddr = 32'h00000010; 
        hburst = 3'b010;      
        hsize = 3'b001;      
        htrans = 2'b11;     
        hwrite = 1;
        hready = 1;
        @(posedge hclk);
       `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionPass Task ended"),UVM_NONE);
    endtask
          
    task CheckForWRAPAssertionFail();
      `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionFail Task started"),UVM_NONE);
      @(posedge hclk);
      haddr = 32'h00001111; 
      hburst = 3'b010;     
      hsize = 3'b001;      
      htrans = 2'b11;      
      hwrite = 1;
      hready = 1;
      @(posedge hclk);
      `uvm_info(name,$sformatf("Check for WRAP (wrapping burst) AssertionPass Task ended"),UVM_NONE);
    endtask

    task CheckTransBusyToSeqAssertionPass();
      `uvm_info(name, $sformatf("%t Check Trans Busy To Seq AssertionPass Task started",$time), UVM_NONE);
      @(posedge hclk);
      htrans = 2'b01;
      hready = 0;
      haddr = 32'h0C0FFEE0;
      hburst = 3'b101;
      @(posedge hclk);
      htrans = 2'b11;
      hready = 0 ;
      haddr = 32'h0C0FFEE0;
      @(posedge hclk);
      `uvm_info(name, $sformatf("%t Check Trans Busy To Seq AssertionPass Task ended",$time), UVM_NONE);
    endtask

    task CheckTransBusyToSeqAssertionFail();
      `uvm_info(name, $sformatf("%t Check Trans Busy To Seq AssertionFail Task started",$time), UVM_NONE);
       @(posedge hclk);
       htrans = 2'b01;
       hready = 0;
       haddr = 32'h0C0FFEE0;
       hburst = 3'b101;
       @(posedge hclk);
       htrans = 2'b11;
       hready = 0 ;
       hburst = 3'b110;
       haddr = 32'h0C0FFEE0;
       @(posedge hclk);
      `uvm_info(name, $sformatf("%t Check Trans Busy To Seq AssertionFail Task ended",$time), UVM_NONE);
    endtask

    task CheckTransBusyToNonSeqAssertionPass();
      `uvm_info(name, $sformatf("%t Check Trans Busy To Non-Seq AssertionPass Task started",$time), UVM_NONE);
      @(posedge hclk);
      htrans = 2'b01;
      hready = 0;
      haddr = 32'hDEADBEEF;
      hburst = 3'b001;
      @(posedge hclk);
      htrans = 2'b10;
      hready = 0 ;
      haddr = 32'hDEADBEEF;
      @(posedge hclk);
      `uvm_info(name, $sformatf("%t Check Trans Busy To Non Seq AssertionPass Task ended",$time), UVM_NONE);
    endtask

    task CheckTransBusyToNonSeqAssertionFail();
      `uvm_info(name, $sformatf("%t Check Trans Busy To Non-Seq AssertionFail Task started",$time), UVM_NONE);
       @(posedge hclk);
       htrans = 2'b01;
       hready = 0;
       haddr = 32'h00000000;
       hburst = 3'b001;
       @(posedge hclk);
       htrans = 2'b10;
       hready = 0 ;
       haddr = 32'h00000004;
       @(posedge hclk);
       `uvm_info(name, $sformatf("%t Check Trans Busy To Non Seq AssertionFail Task ended",$time), UVM_NONE);
     endtask

     task CheckTransIdleToNonSeqAssertionPass();
       `uvm_info(name, $sformatf("%t Check Trans Idle To Non-Seq AssertionPass Task started",$time), UVM_NONE);
       @(posedge hclk);
       htrans = 2'b00;
       hready = 0;
       @(posedge hclk);
       htrans = 2'b10;
       hready = 0 ;
       haddr = 32'h00000004;
       @(posedge hclk);
       `uvm_info(name, $sformatf("%t Check Trans Idle To Non Seq AssertionPass Task ended",$time), UVM_NONE);
     endtask

     task CheckTransIdleToNonSeqAssertionFail();
       `uvm_info(name, $sformatf("%t Check Trans Idle To Non-Seq AssertionFail Task started",$time), UVM_NONE);
       @(posedge hclk);
       htrans = 2'b00;
       hready = 0;
       @(posedge hclk);
       htrans = 2'b10;
       hready = 0 ;
       haddr = 32'h00000004;
       @(posedge hclk);
       `uvm_info(name, $sformatf("%t Check Idle Busy To Non Seq AssertionFail Task ended",$time), UVM_NONE);
     endtask


     task checkAddrStabilityAssertionPass();
       `uvm_info(name, $sformatf("%tAddress  stability started",$time), UVM_NONE);
        @(posedge hclk);
        htrans = 2'b10; 
        haddr = 32'hA0001000; 
        hready = 0; 
        @(posedge hclk);
        haddr = 32'hA0001000; 
        @(posedge hclk);
        hready = 1;
        @(posedge hclk);
        htrans = 2'b11; 
        haddr = 32'hA0001004;
        @(posedge hclk);
       `uvm_info(name, $sformatf("%tAddress stability Task ended",$time), UVM_NONE);
     endtask
  
     task checkAddrStabilityAssertionFail();
       `uvm_info(name, $sformatf("%tAddress  stability started",$time), UVM_NONE);
        @(posedge hclk);
        htrans = 2'b10; 
        haddr = 32'hA0001000; 
        hready = 0; 
        @(posedge hclk);
        haddr = 32'hA0001004; 
        @(posedge hclk);
        hready = 1;
        @(posedge hclk);
        htrans = 2'b11; 
        haddr = 32'hA0001008;
        @(posedge hclk);
        `uvm_info(name, $sformatf("%tAddress stability Task ended",$time), UVM_NONE);
      endtask
endmodule
`endif
