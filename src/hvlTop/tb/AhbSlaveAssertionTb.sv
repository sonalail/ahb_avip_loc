`ifndef AHBSLAVEASSERTIONTB_INCLUDED_
`define AHBSLAVEASSERTIONTB_INCLUDED_

import AhbGlobalPackage::*;
import uvm_pkg::*;

`include "uvm_macros.svh"

module AhbSlaveAssertionTb;

  reg        		hclk;
  reg         		hresetn;
  reg         		hreadyout;
  reg [DATA_WIDTH-1:0]  hrdata;
  reg 		 [1:0]  hresp;
  reg [ADDR_WIDTH-1:0]  haddr;
  reg            [1:0]  htrans;
  reg       	        hwrite;
  reg            [2:0]  hsize;
  reg            [2:0]  hburst;
  reg                   hselx;
  reg [DATA_WIDTH-1:0]  hwdata;
  reg            [3:0]  hprot;
  reg                   hexokay;
  reg            [3:0]  hwstrb;

  AhbSlaveAssertion ahbslaveassertions_u (.hclk(hclk),
    .hresetn(hresetn),
    .hreadyout(hreadyout),
    .hrdata(hrdata),
    .hresp(hresp),
    .haddr(haddr),
    .htrans(htrans),
    .hwrite(hwrite),
    .hsize(hsize),
    .hburst(hburst),
    .hselx(hselx),
    .hwdata(hwdata),
    .hprot(hprot),
    .hexokay(hexokay),
    .hwstrb(hstrb)
  );

  string name = "AhbSlaveAssertionTb";
  
  always begin
    #5 hclk = ~hclk;  // 100 MHz clock (10ns period)
  end


  initial begin
    hclk = 0;
    hresetn = 0;
    #15 hresetn = 1;
  end

  initial begin
    InitialSignals();
    
    ValidReadTransactionAssertionPass();
    ValidReadTransactionAssertionFail();
    
    InvalidReadwithHRESPErrorAssertionPass();
    HrespIsOkayForValidTransactionAssertionFail();
    
    WriteTransactionAssertionPass();
    
    BurstTransactionIncrementAssertionPass();
    InvalidBurstTypeAssertionPass();
    InvalidBurstTypeAssertionFail();
    
    IdleStatewithHrsepErrorAssertionPass();
    IdleStatewithHrespErrorAssertionFail();
    
    HsizeDoesNotMatchDataWidthAssertionFail();
    
    $finish;
  end
  
  task InitialSignals();
    `uvm_info(name,$sformatf("When reset is high Initialize the signals "),UVM_NONE);
     @(posedge hclk);
     if(hresetn==0)
       begin
         hreadyout = 0;
         hrdata = 32'b0;
         hresp = 2'b00;
         haddr = 32'b0;
         htrans = 2'b00;
         hwrite = 1'b0;
         hsize = 3'b010;  
         hburst = 3'b000; 
         hselx = 1'b0;
         hwdata = 32'b0;
         hprot = 4'b0000;
         hexokay = 1'b0;
         hwstrb = 4'b1111;
       end
     `uvm_info(name,$sformatf("When_arvalidIsAsserted_Then_sameClkAraddrIsNotUnknown_Expect_AssertionPass Task Ended"),UVM_NONE);
   endtask

  
  task ValidReadTransactionAssertionPass();
    `uvm_info(name,$sformatf("Valid Read Transaction Assertion Pass Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10; 
    hreadyout = 1;
    hwrite = 0;      
    haddr = 32'h0000_1000;   
    hresp = 2'b00;   
    @(posedge hclk);
    hrdata = 32'hA5A5A5A5; 
    @(posedge hclk);
    `uvm_info(name,$sformatf("Valid Read Transaction Assertion Pass Ended "),UVM_NONE);
  endtask
  
  task ValidReadTransactionAssertionFail();
    `uvm_info(name,$sformatf("Invalid Read Transaction (Fail Assertion) Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  
    hreadyout = 1;
    hwrite = 0;    
    haddr = 32'h0000_1000;   
    hresp = 2'b00;   
    @(posedge hclk);
    hrdata = 32'hx;
    @(posedge hclk); 
    `uvm_info(name,$sformatf("Invalid Read Transaction (Fail Assertion) Ended "),UVM_NONE);
  endtask
  
  task InvalidReadwithHRESPErrorAssertionPass();
    `uvm_info(name,$sformatf("Invalid Read with HRESP Error Assertion Pass Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b00;  
    hreadyout = 1;
    hresp = 2'b01;   
    @(posedge hclk);
    `uvm_info(name,$sformatf("Invalid Read with HRESP Error Assertion Pass Ended"),UVM_NONE);
  endtask
    
  task WriteTransactionAssertionPass();
    `uvm_info(name,$sformatf("Write Transaction Assertion Pass Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b01;  
    hreadyout = 1;
    hwrite = 1;      
    haddr = 32'h0000_2000;   
    hresp = 2'b00;   
    @(posedge hclk);
    hwdata = 32'hDEAD_BEEF; 
    @(posedge hclk); 
    `uvm_info(name,$sformatf("Write Transaction Pass Assertion Ended"),UVM_NONE);
  endtask
    
  task InvalidBurstTypeAssertionFail();
    `uvm_info(name,$sformatf("Invalid Burst Type Assertion Fail Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  
    hburst = 3'b101;
    hreadyout = 1;
    hresp = 2'b00;
    @(posedge hclk);
    `uvm_info(name,$sformatf("Invalid Burst Type Assertion Fail Ended"),UVM_NONE);
  endtask

  task BurstTransactionIncrementAssertionPass();
    `uvm_info(name,$sformatf("Burst Transaction (INCR) Assertion Pass Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  
    hburst = 3'b001; 
    hreadyout = 1;
    haddr = 32'h0000_3000;
    hresp = 2'b00;
    @(posedge hclk);
    `uvm_info(name,$sformatf("Burst Transaction (INCR) Assertion Pass Ended"),UVM_NONE);
  endtask
   
  task IdleStatewithHrespErrorAssertionFail();
    `uvm_info(name,$sformatf("Idle State with HRESP ERROR Assertion Fail Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b00; 
    hreadyout = 1;
    hresp = 2'b00;   
    @(posedge hclk);
    `uvm_info(name,$sformatf("Idle State with HRESP ERROR Assertion Fail Ended"),UVM_NONE);
  endtask

  task InvalidBurstTypeAssertionPass();
    `uvm_info(name,$sformatf("Invalid Burst Type Assertion Pass Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  
    hburst = 3'b101;
    hreadyout = 1;
    hresp = 2'b00;
    @(posedge hclk);
    `uvm_info(name,$sformatf("Invalid Burst Type Assertion Pass Ended"),UVM_NONE);
  endtask

  task HsizeDoesNotMatchDataWidthAssertionFail();
    `uvm_info(name,$sformatf("HSIZE does not match data width Assertion Fail Started "),UVM_NONE);
    @(posedge hclk);
    hreadyout = 1;
    htrans = 2'b10; 
    hsize = 3'b110;
    @(posedge hclk);
    `uvm_info(name,$sformatf("HSIZE does not match data width Assertion Fail Ended"),UVM_NONE);
  endtask
  
  task IdleStatewithHrsepErrorAssertionPass();
    `uvm_info(name,$sformatf("Idle State with HRESP ERROR Assertion Pass Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b00; 
    hreadyout = 1;
    hresp = 2'b01;  
    @(posedge hclk);
    `uvm_info(name,$sformatf("Idle State with HRESP ERROR Assertion Pass Ended"),UVM_NONE);
  endtask
   
  task HrespIsOkayForValidTransactionAssertionFail();
    `uvm_info(name,$sformatf("HRESP is OKAY for valid transaction Assertion Fail Started "),UVM_NONE);
    @(posedge hclk);
    hreadyout = 1;
    htrans = 2'b10;
    hresp = 1'b1; 
    @(posedge hclk);      
    `uvm_info(name,$sformatf("HRESP is OKAY for valid transaction Assertion Fail Ended"),UVM_NONE);
  endtask
  
  initial begin
    $monitor("Time=%0t, htrans=%b, hresp=%b, hreadyout=%b, hrdata=%h, haddr=%h, hwrite=%b, hburst=%b",
             $time, htrans, hresp, hreadyout, hrdata, haddr, hwrite, hburst);
  end

endmodule
`endif

