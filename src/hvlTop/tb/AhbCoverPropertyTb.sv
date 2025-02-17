`ifndef AHBCOVERPROPERTYTB_INCLUDED_
`define AHBCOVERPROPERTYTB_INCLUDED_

import AhbGlobalPackage::*;

import uvm_pkg::*;

`include "uvm_macros.svh"

module AhbCoverPropertyTb;
  reg                      hclk;
  reg                      hresetn;
  reg     [ADDR_WIDTH-1:0] haddr;
  reg     [DATA_WIDTH-1:0] hwdata;
  reg                [2:0] hsize;
  reg                [2:0] hburst;
  reg                [1:0] htrans;
  reg                      hwrite;
  reg                      hready;
  reg                      hresp;
  reg                      hexcl;
  reg    [HPROT_WIDTH-1:0] hprot;
  reg  [HMASTER_WIDTH-1:0] hmaster;
  reg                      hmastlock;
  reg                      htransValid;
  reg                      hreadyout;
  reg     [DATA_WIDTH-1:0] hrdata;
  reg   [NO_OF_SLAVES-1:0] hselx;
  reg                      hexokay;
  reg [(DATA_WIDTH/8)-1:0] hwstrb ;
  reg     [DATA_WIDTH-1:0] hwdataValid;

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

  always begin
    #5 hclk = ~hclk;
  end

  initial begin
    hclk = 0;
    hresetn = 0;
    #15 hresetn = 1;
  end

  initial begin
   // writeDataIsEqualToReadDataAndBothTheAddressIsSameInNonSeqState();
    //writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInNonSeqState();

   // writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrementBurst();
   // writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrementBurst();

   // writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap4Burst();
   // writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap4Burst();

    writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement4Burst();
    //writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement4Burst();

    //writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap8Burst();
    //writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap8Burst();

    //writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement8Burst();
    //writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement8Burst();

    //writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap16Burst();
    //writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap16Burst();

    //writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement16Burst();
    //writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement16Burst();

    $finish;
  end


  //NON - SEQ
  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInNonSeqState();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Non-Seq State task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00;
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010;
    hburst  = 3'b000;
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1;

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1;
    htrans  = 2'b10;
    haddr   = 32'h1000_1004;
    hwdata  = 32'h1234_abcd;
    hburst  = 3'b000;
    hsize   = 3'b010;

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0;
    htrans  = 2'b10;
    haddr   = 32'h1000_1004;
    hburst  = 3'b000;
    hsize   = 3'b010;
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Non-Seq State task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInNonSeqState();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Non-Seq State task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00;
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010;
    hburst  = 3'b000;
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hwrite  = 1;
    htrans  = 2'b10;
    haddr   = 32'h1000;
    hwdata  = 32'hA5A5A5A5;
    hready  = 1;
    hresp   = 0;

    @(posedge hclk);
    hwrite  = 0;
    htrans  = 2'b10;
    haddr   = 32'h2000;
    hready  = 1;
    hresp   = 0;
    hrdata  = 32'hA5A5A5A5;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Non-Seq State task ended"),UVM_NONE);
  endtask

  //SEQ
  //INCREMENT BURST

  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrementBurst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; 
    hburst  = 3'b000; 
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; 
    htrans  = 2'b11; 
    haddr   = 32'h1000_1004; 
    hwdata  = 32'h1234_abcd;
    hburst  = 3'b001;
    hsize   = 3'b001; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; 
    htrans  = 2'b11; 
    haddr   = 32'h1000_1004 + (hsize<<1); 
    hburst  = 3'b001; 
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment Burst task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrementBurst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; 
    hburst  = 3'b000; 
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; 
   
    @(posedge hclk);
    hwrite  = 1;
    htrans  = 2'b10;  
    hburst  = 3'b001;
    haddr   = 32'h1000_0000;
    hwdata  = 32'hA5A5A5A5;
    hready  = 1;
    hresp   = 0;

    @(posedge hclk);
    hwrite  = 1;
    htrans  = 2'b11; 
    hburst  = 3'b001; 
    haddr   = 32'h1000_0005;
    hwdata  = 32'h5A5A5A5A;
    hready  = 1;
    hresp   = 0;

    @(posedge hclk);
    hwrite  = 0;
    htrans  = 2'b11; 
    hburst  = 3'b001;
    haddr   = 32'h1000_0000; 
    hrdata  = 32'h5A5A5A5A; 
    hready  = 1;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment Burst task ended"),UVM_NONE);
  endtask

  //WRAP4 BURST
  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap4Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap4 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hburst = 3'b010; 
    htrans = 2'b11;  
    hready = 1;
    haddr = 32'h10000000; 
    hwdata = 32'hA5A5A5A5;
    hrdata = 32'hZZZZZZZZ;
    hwrite = 1; 

    @(posedge hclk) haddr = 32'h10000004; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000008; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1; 
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h1000000C;
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000000; 
    hwrite = 0; 
    hrdata = 32'hA5A5A5A5;

    @(posedge hclk); 
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap4 Burst task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap4Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The AddressIs Not Same In Seq State Wrap4 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hburst = 3'b010;
    htrans = 2'b11;
    hready = 1;
    haddr = 32'h10000000; 
    hwdata = 32'hA5A5A5A5; 
    hrdata = 32'hZZZZZZZZ; 
    hwrite = 1;      

    @(posedge hclk) haddr = 32'h10000004;
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000008;
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h1000000C; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h00000000; 
    hwrite = 0; 
    hrdata = 32'hA5A5A5A5;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The AddressIs Not Same In Seq State Wrap4 Burst task ended"),UVM_NONE);
  endtask

  //INCREMENT4 BURST
  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement4Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment4 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; 
    hburst  = 3'b000; 
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; 
    htrans  = 2'b10; 
    haddr   = 32'h1000_1004; 
    hwdata  = 32'h1234_abcd;
    hburst  = 3'b011; 
    hsize   = 3'b001;

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; 
    htrans  = 2'b11; 
    haddr   = 32'h1000_1008; 
    hburst  = 3'b011;
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment4 Burst task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement4Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment4 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010;
    hburst  = 3'b000;
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1;
    htrans  = 2'b10; 
    haddr   = 32'h1000_1004; 
    hwdata  = 32'h1234_abcd; 
    hburst  = 3'b011; 
    hsize   = 3'b001; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; 
    htrans  = 2'b11; 
    haddr   = 32'h1000_1004; 
    hburst  = 3'b011; 
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment4 Burst task ended"),UVM_NONE);
  endtask

  //WRAP8 BURST

  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap8Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap8 Burst task Started"),UVM_NONE);

 
    @(posedge hclk);
    hburst = 3'b100; 
    htrans = 2'b11;   
    hready = 1;
    haddr = 32'h10000000; 
    hwdata = 32'hA5A5A5A5; 
    hrdata = 32'hZZZZZZZZ; 
    hwrite = 1;      

    @(posedge hclk) haddr = 32'h10000004; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000008;
    hwdata = 32'h5A5A5A5A;
    hwrite = 1;  
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h1000000C;
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000010; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000014; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;  
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000018; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h1000001C; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;  
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000000; 
    hwrite = 0;  
    hrdata = 32'hA5A5A5A5; 

    @(posedge hclk);  
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap8 Burst task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap8Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The AddressIs Not Same In Seq State Wrap8 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hburst = 3'b100;  
    htrans = 2'b11;   
    hready = 1;
    haddr = 32'h10000000; 
    hwdata = 32'hA5A5A5A5; 
    hrdata = 32'hZZZZZZZZ; 
    hwrite = 1;

    @(posedge hclk) haddr = 32'h10000004; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000008; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h1000000C;
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000010;
    hwdata = 32'h5A5A5A5A;
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000014; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000018; 
    hwdata = 32'h5A5A5A5A;
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h1000001C; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h00000000; 
    hwrite = 0;  
    hrdata = 32'hA5A5A5A5;

    @(posedge hclk); 
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address\Is Not Same In Seq State Wrap8 Burst task ended"),UVM_NONE);
  endtask


  //INCRMENT 8
  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement8Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment8 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; 
    hburst  = 3'b000; 
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1;

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1;
    htrans  = 2'b10; 
    haddr   = 32'h1000_1004; 
    hwdata  = 32'h1234_abcd; 
    hburst  = 3'b101;
    hsize   = 3'b001; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0;
    htrans  = 2'b11;
    haddr   = 32'h1000_100C; 
    hburst  = 3'b011; 
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment8 Burst task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement8Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment8 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010;
    hburst  = 3'b000; 
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; 
    
    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; 
    htrans  = 2'b10; 
    haddr   = 32'h1000_1004;
    hwdata  = 32'h1234_abcd;
    hburst  = 3'b101;
    hsize   = 3'b001;

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; 
    htrans  = 2'b11; 
    haddr   = 32'h1000_1000; 
    hburst  = 3'b011; 
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment8 Burst task ended"),UVM_NONE);
  endtask


  //WRAP16 BURST

  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap16Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap16 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hburst = 3'b110;  
    htrans = 2'b11;  
    hready = 1;
    haddr = 32'h10000000; 
    hwdata = 32'hA5A5A5A5;
    hrdata = 32'hZZZZZZZZ; 
    hwrite = 1;    

    @(posedge hclk) haddr = 32'h10000004; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000008; 
    hwdata = 32'h5A5A5A5A;
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h1000000C; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000010;
    hwdata = 32'h5A5A5A5A;
    hwrite = 1; 
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000014;
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11; 
    @(posedge hclk) haddr = 32'h10000018;
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11;  
    @(posedge hclk) haddr = 32'h1000001C;
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1; 
    htrans = 2'b11; 
    
    @(posedge hclk) haddr = 32'h10000020; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000024; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000028; 
    hwdata = 32'h5A5A5A5A;
    hwrite = 1;  
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h1000002C; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000030;
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000034; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000038; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h1000003C; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000000; 
    hwrite = 0;  
    hrdata = 32'hA5A5A5A5; 

    @(posedge hclk); 
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap16 Burst task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap16Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The AddressIs Not Same In Seq State Wrap16 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hburst = 3'b110;  
    htrans = 2'b11;   
    hready = 1;
    haddr = 32'h10000000; 
    hwdata = 32'hA5A5A5A5; 
    hrdata = 32'hZZZZZZZZ;  
    hwrite = 1;      

    @(posedge hclk) haddr = 32'h10000004; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h10000008;
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h1000000C; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11; 
    
    @(posedge hclk) haddr = 32'h10000010; 
    hwdata = 32'h5A5A5A5A;
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000014;
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1; 
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000018; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h1000001C; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;  
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000020;
    hwdata = 32'h5A5A5A5A;
    hwrite = 1; 
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000024; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000028; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h1000002C; 
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11;

    @(posedge hclk) haddr = 32'h10000030; 
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000034; 
    hwdata = 32'hA5A5A5A5;
    hwrite = 1; 
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h10000038;
    hwdata = 32'h5A5A5A5A; 
    hwrite = 1; 
    htrans = 2'b11; 

    @(posedge hclk) haddr = 32'h1000003C;
    hwdata = 32'hA5A5A5A5; 
    hwrite = 1;  
    htrans = 2'b11;  

    @(posedge hclk) haddr = 32'h00000000;
    hwrite = 0; 
    hrdata = 32'hA5A5A5A5; 

    @(posedge hclk);  
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The AddressIs Not Same In Seq State Wrap16 Burst task ended"),UVM_NONE);
  endtask


  //INCREMENT16 BURST

  task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement16Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment16 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010; 
    hburst  = 3'b000;
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1; 
    htrans  = 2'b10;
    haddr   = 32'h1000_1004;
    hwdata  = 32'h1234_abcd; 
    hburst  = 3'b111;
    hsize   = 3'b001; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0;
    htrans  = 2'b11;
    haddr   = 32'h1000_1014; 
    hburst  = 3'b011; 
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment16 Burst task ended"),UVM_NONE);
  endtask

  task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement16Burst();
    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment16 Burst task Started"),UVM_NONE);

    @(posedge hclk);
    hwrite  = 1'b0;
    htrans  = 2'b00; 
    haddr   = 32'hxxxx_xxxx;
    hwdata  = 32'hxxxx_xxxx;
    hsize   = 3'b010;
    hburst  = 3'b000;
    hready  = 1'b0;
    hrdata  = 32'hxxxx_xxxx;

    @(posedge hclk);
    hready  = 1'b1; 

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b1;
    htrans  = 2'b10; 
    haddr   = 32'h1000_1004;
    hwdata  = 32'h1234_abcd;
    hburst  = 3'b111;
    hsize   = 3'b001;

    @(posedge hclk);
    hready = 1;
    hwrite  = 1'b0; 
    htrans  = 2'b11;
    haddr   = 32'h1000_1000;
    hburst  = 3'b011; 
    hrdata  = 32'h1234_abcd;
    hresp   = 0;

    @(posedge hclk);
    @(posedge hclk);

    `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment16 Burst task ended"),UVM_NONE);
  endtask

  initial begin
    $monitor("Time=%0t, htrans=%b, hresp=%b, hreadyout=%b, hsize = %b , hwdata =%h, hrdata=%h, haddr=%h, hwrite=%b, hburst=%b",
             $time, htrans, hresp, hreadyout, hsize, hwdata, hrdata, haddr, hwrite, hburst);
  end

endmodule
`endif

