`ifndef AHBSLAVEASSERTIONTB_INCLUDED_
`define AHBSLAVEASSERTIONTB_INCLUDED_

import AhbGlobalPackage::*;

import uvm_pkg::*;
`include "uvm_macros.svh"

module AhbSlaveAssertionTb;

  // Testbench signals (these will drive the interface signals)
  reg         hclk;
  reg         hresetn;
  reg         hreadyout;
  reg [DATA_WIDTH-1:0]  hrdata;
  reg [1:0]   hresp;
  reg [ADDR_WIDTH-1:0]  haddr;
  reg [1:0]   htrans;
  reg         hwrite;
  reg [2:0]   hsize;
  reg [2:0]   hburst;
  reg         hselx;
  reg [DATA_WIDTH-1:0]  hwdata;
  reg [3:0]   hprot;
  reg         hexokay;
  reg [3:0]   hwstrb;

  // Instantiate the interface for Slave Assertions
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
  // Clock generation
  always begin
    #5 hclk = ~hclk;  // 100 MHz clock (10ns period)
  end

  // Initial block to apply stimulus and reset
  initial begin
    hclk = 0;
    hresetn = 0;
    #15 hresetn = 1;
  end

  initial begin
    InitialSignals();
    
    ValidReadTransaction();
    ValidReadTransactionFail();
    
    InvalidReadwithHRESPError();
    HrespIsOkayForValidTransactionFail();
    
    WriteTransactionPassAssertion();
    
    BurstTransactionIncrement();
    InvalidBurstType();
    InvalidBurstTypeFail();
    
    IdleStatewithHrsepError();
    IdleStatewithHrespErrorFail();
    
    HsizeDoesNotMatcheDataWidthFail();
    
    $finish;
  end
  

  // Initialize signals
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
         hsize = 3'b010;  // Word transfer
         hburst = 3'b000; // Single burst
         hselx = 1'b0;
         hwdata = 32'b0;
         hprot = 4'b0000;
         hexokay = 1'b0;
         hwstrb = 4'b1111;
       end
     `uvm_info(name,$sformatf("When_arvalidIsAsserted_Then_sameClkAraddrIsNotUnknown_Expect_AssertionPass Task Ended"),UVM_NONE);
   endtask

    // Test 1: Valid Read Transaction
  task ValidReadTransaction();
    `uvm_info(name,$sformatf("Valid Read Transaction Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  // NONSEQ transaction
    hreadyout = 1;
    hwrite = 0;      // Read
    hrdata = 32'hA5A5A5A5;  // Read data
    haddr = 32'h0000_1000;   // Example address
    hresp = 2'b00;   // OKAY response
    #20;
    `uvm_info(name,$sformatf("Valid Read Transaction Ended "),UVM_NONE);
  endtask

  // Test 1.1: Invalid Read Transaction(Fail Assertion)
  task ValidReadTransactionFail();
    `uvm_info(name,$sformatf("Invalid Read Transaction (Fail Assertion) Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  // NONSEQ transaction
    hreadyout = 1;
    hwrite = 0;      // Read
    hrdata = 32'hx;  // Read data
    haddr = 32'h0000_1000;   // Example address
    hresp = 2'b00;   // OKAY response
    #20;
    `uvm_info(name,$sformatf("Invalid Read Transaction (Fail Assertion) Ended "),UVM_NONE);
  endtask
  
    // Test 2: Invalid Read with HRESP Error
  task InvalidReadwithHRESPError();
    `uvm_info(name,$sformatf("Invalid Read with HRESP Error Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b00;  // IDLE
    hreadyout = 1;
    hresp = 2'b01;   // ERROR response
    #20;
    `uvm_info(name,$sformatf("Invalid Read with HRESP Error Ended"),UVM_NONE);
  endtask
    
  // Test 3: Write Transaction (Pass Assertion)
  task WriteTransactionPassAssertion();
    `uvm_info(name,$sformatf("Write Transaction Pass Assertion Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b01;  // BUSY transaction
    hreadyout = 1;
    hwrite = 1;      // Write
    hwdata = 32'hDEAD_BEEF;  // Write data
    haddr = 32'h0000_2000;   // Example address
    hresp = 2'b00;   // OKAY response
    #20;
    `uvm_info(name,$sformatf("Write Transaction Pass Assertion Ended"),UVM_NONE);
  endtask
    
  
  // Test 3.1: Invalid Burst Type (Fail Assertion)
  task InvalidBurstTypeFail();
    `uvm_info(name,$sformatf("Invalid Burst Type Fail Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  // NONSEQ
    hburst = 3'b101; // Invalid burst type
    hreadyout = 1;
    hresp = 2'b00;
    #20;
    `uvm_info(name,$sformatf("Invalid Burst Type Fail Ended"),UVM_NONE);
  endtask
  
  
  // Test 4: Burst Transaction (INCR)
  task BurstTransactionIncrement();
    `uvm_info(name,$sformatf("Burst Transaction (INCR) Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  // NONSEQ
    hburst = 3'b001; // INCR burst
    hreadyout = 1;
    haddr = 32'h0000_3000;
    hresp = 2'b00;
    #20;
    `uvm_info(name,$sformatf("Burst Transaction (INCR) Ended"),UVM_NONE);
  endtask
   
  
  // Test 4.1: Idle State with HRESP ERROR(Fail assertion)
  task IdleStatewithHrespErrorFail();
    `uvm_info(name,$sformatf("Idle State with HRESP ERROR Fail Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b00;  // IDLE
    hreadyout = 1;
    hresp = 2'b00;   // OKAY  response
    #20;
    `uvm_info(name,$sformatf("Idle State with HRESP ERROR Fail Ended"),UVM_NONE);
  endtask
  
  // Test 5: Invalid Burst Type
  task InvalidBurstType();
    `uvm_info(name,$sformatf("Invalid Burst Type Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b10;  // NONSEQ
    hburst = 3'b101; // Invalid burst type
    hreadyout = 1;
    hresp = 2'b00;
    #20;
    `uvm_info(name,$sformatf("Invalid Burst Type Ended"),UVM_NONE);
  endtask
  
  
  //Test 5.1 :HSIZE does not matche data width)(Fail Assertion)
  task HsizeDoesNotMatcheDataWidthFail();
    `uvm_info(name,$sformatf("HSIZE does not matche data width Fail Started "),UVM_NONE);
    @(posedge hclk);
    hreadyout = 1;
    htrans = 2'b10; //NONSEQ
    hsize = 3'b110;
    #20;
    `uvm_info(name,$sformatf("HSIZE does not matche data width Fail Ended"),UVM_NONE);
  endtask
  
  // Test 6: Idle State with HRESP ERROR
  task IdleStatewithHrsepError();
    `uvm_info(name,$sformatf("Idle State with HRESP ERROR Started "),UVM_NONE);
    @(posedge hclk);
    htrans = 2'b00;  // IDLE
    hreadyout = 1;
    hresp = 2'b01;   // ERROR response
    #20;
   `uvm_info(name,$sformatf("Idle State with HRESP ERROR Ended"),UVM_NONE);
  endtask
   
   //Test 6.1 :HRESP is OKAY for valid transaction (Fail assertion)
  task HrespIsOkayForValidTransactionFail();
    `uvm_info(name,$sformatf("HRESP is OKAY for valid transaction Fail Started "),UVM_NONE);
    @(posedge hclk);
    hreadyout = 1; // Ready signal is high
    htrans = 2'b10; // NONSEQ (valid transaction)
    hresp = 1'b1; // ERROR response
    #20;       
    `uvm_info(name,$sformatf("HRESP is OKAY for valid transaction Fail Ended"),UVM_NONE);
  endtask
  
  // Monitor the assertion errors
  initial begin
    $monitor("Time=%0t, htrans=%b, hresp=%b, hreadyout=%b, hrdata=%h, haddr=%h, hwrite=%b, hburst=%b",
             $time, htrans, hresp, hreadyout, hrdata, haddr, hwrite, hburst);
  end

endmodule
`endif

