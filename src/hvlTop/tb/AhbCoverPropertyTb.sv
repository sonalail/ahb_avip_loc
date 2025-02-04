
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
  .hready(hready),
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

initial begin
  InitialSignals();
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
  `uvm_info(name,$sformatf("Initialization done"),UVM_NONE);
endtask

//NON - SEQ

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInNonSeqState();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Non-Seq State task Started"),UVM_NONE);
    @(posedge hclk);
  hwrite = 1;
  htrans =2'b10;
  hready = 1;
  hwdata = 32'hDEADBEEF;
  haddr = 32'hFFFFFFFF;
  #10;
  hrdata = 32'hDEADBEEF;
  hresp = 0;
  haddr = 32'hFFFFFFFF;
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Non-Seq State task ended"),UVM_NONE);
  
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInNonSeqState();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Non-Seq State task Started"),UVM_NONE);
    @(posedge hclk);
  hwrite = 1;
  htrans =2'b10;
  hready = 1;
  hwdata = 32'hDEADBEEF;
  haddr = 32'hFFFFFFFF;
  #10;
  hrdata = 32'hDEADBEEF;
  hresp = 0;
  haddr = 32'hFFFFFFF0; 
  #20;
   `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Non-Seq State task ended"),UVM_NONE);
endtask

//SEQ 
//INCREMENT BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrementBurst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b001;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000002; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment Burst task ended"),UVM_NONE);
endtask


task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrementBurst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b001;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000001; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment Burst task ended"),UVM_NONE);
endtask

//WRAP4 BURST
task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap4Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap4 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b010;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000004; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap4 Burst task ended"),UVM_NONE);
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap4Burst();
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap4 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b010;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000000; 
  #20;
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap4 Burst task ended"),UVM_NONE);
endtask

//INCREMENT4 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement4Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment4 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b011;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000005; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment4 Burst task ended"),UVM_NONE);
endtask

  
task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement4Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment4 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b011;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000000; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment4 Burst task ended"),UVM_NONE);
endtask

//WRAP8 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap8Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap8 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b100;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000004;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h0000000A; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap8 Burst task ended"),UVM_NONE);
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap8Burst();
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap8 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b100;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000004;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000000; 
  #20;
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap8 Burst task ended"),UVM_NONE);
endtask

//INCRMENT 8

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement8Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment8 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b101;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000004;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h0000000C; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment8 Burst task ended"),UVM_NONE);
endtask

  
task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement8Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment8 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b101;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000000; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment8 Burst task ended"),UVM_NONE);
endtask


//WRAP16 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap16Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap16 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b110;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h0000000A;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000016; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Wrap16 Burst task ended"),UVM_NONE);
endtask

task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap16Burst();
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap16 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b110;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h0000000A;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000000; 
  #20;
`uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Wrap16 Burst task ended"),UVM_NONE);
endtask

//INCREMENT16 BURST

task writeDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement16Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment16 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b111;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000000;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000010; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Same In Seq State Increment16 Burst task ended"),UVM_NONE);
endtask

  
task writeDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement16Burst();
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment16 Burst task Started"),UVM_NONE);
  hwrite = 1;
  htrans =2'b11;
  hready = 1;
  hburst = 3'b111;
  hwdata = 32'h0C0FFEE0;
  haddr = 32'h00000001;
  hsize = 3'b010;
  #10;
  hrdata = 32'h0C0FFEE0;
  hresp = 0;
  haddr = 32'h00000000; 
  #20;
  `uvm_info(name,$sformatf("write Data Is Equal To Read Data And Both The Address Is Not Same In Seq State Increment16 Burst task ended"),UVM_NONE);
endtask

 initial begin
   $monitor("Time=%0t, htrans=%b, hresp=%b, hreadyout=%b, hsize = %b , hwdata =%h, hrdata=%h, haddr=%h, hwrite=%b, hburst=%b",
             $time, htrans, hresp, hreadyout,hsize, hwdata, hrdata, haddr, hwrite, hburst);
  end

endmodule
`endif




