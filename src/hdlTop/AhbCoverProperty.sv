`ifndef AHBCOVERPROPERTYINCLUDED_
`define AHBCOVERPROPERTYINCLUDED_

import AhbGlobalPackage::*;

interface AhbCoverProperty (input hclk,
                            input hresetn,
                            input [ADDR_WIDTH-1:0] haddr,
                            input [NO_OF_SLAVES-1:0] hselx,
                            input [2:0] hburst,
                            input hmastlock,
                            input [HPROT_WIDTH-1:0] hprot,
                            input [2:0] hsize,
                            input hnonsec,
                            input hexcl,
                            input [HMASTER_WIDTH-1:0] hmaster,
                            input [1:0] htrans,
                            input [DATA_WIDTH-1:0] hwdata,
                            input [(DATA_WIDTH/8)-1:0] hwstrb,
                            input hwrite,
                            input [DATA_WIDTH-1:0] hrdata,
                            input hreadyout,
                            input hresp,
                            input hexokay,
                            input hready
                       );
  
  import uvm_pkg::*;
  `include "uvm_macros.svh";

  initial begin
    `uvm_info("AhbCoverProperty","AhbCoverProperty",UVM_LOW);
  end
  
  
  //non-seq
  property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInNonSeqState;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10) && hready)
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == $past(haddr)));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInNonSeqState;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10) && hready)
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != $past(haddr)));
  endproperty
  
  //seq
  /*property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateSingleBurst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b11) && hready && (hburst == 3'b000))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == $past(haddr)+1));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateSingleBurst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b11) && hready && (hburst == 3'b000))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != $past(haddr)+1));
  endproperty
  */
 
   property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrementBurst;
    @(posedge hclk) disable iff (!hresetn)
     (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b001))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == $past(haddr)+1));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrementBurst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 ||htrans == 2'b11) && hready && (hburst == 3'b001))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != $past(haddr)+1));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap4Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b010))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == (($past(haddr,4)))));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap4Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b010))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != (($past(haddr,4)))));
  endproperty
         
         
  property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement4Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b011))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == ($past(haddr)+4)));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement4Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b011))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != ($past(haddr)+4)));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap8Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b11) && hready && (hburst == 3'b100))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == (($past(haddr,8)))));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap8Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b100))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != (($past(haddr,8)))));
  endproperty  
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement8Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b101))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == ($past(haddr)+8)));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement8Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b101))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != ($past(haddr)+8)));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap16Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b110))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == (($past(haddr,16)))));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap16Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b110))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != (($past(haddr,16)))));
  endproperty
  
    property WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement16Burst;
    @(posedge hclk) disable iff (!hresetn)
      (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b111))
      |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr == ($past(haddr)+16)));
  endproperty
  
  property WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement16Burst;
    @(posedge hclk) disable iff (!hresetn)
    (hwrite && (htrans == 2'b10 || htrans == 2'b11) && hready && (hburst == 3'b111))
    |=> ((hrdata == $past(hwdata)) && hresp == 0 && (haddr != ($past(haddr)+16)));
  endproperty



  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATANONSEQ : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInNonSeqState)
    $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA NON SEQ : COVERED");

  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATANONSEQ : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInNonSeqState)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA NON SEQ : COVERED");
    
  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATASEQINCR : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrementBurst)
     $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA IN SEQ STATE FOR INCREMENT BURST : COVERED");

  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATASEQINCR : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrementBurst)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA IN SEQ STATE FOR INCREMENT BURST : COVERED");
     
  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATASEQWRAP4 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap4Burst)
    $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA IN SEQ STATE FOR WRAP4 BURST : COVERED");

  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATASEQWRAP4 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap4Burst)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA IN SEQ STATE FOR WRAP4 BURST : COVERED");
     
  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATASEQINCR4 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement4Burst)
    $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA IN SEQ STATE FOR INCR4 BURST : COVERED");

  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATASEQINCR4 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement4Burst)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA IN SEQ STATE FOR INCR4 BURST : COVERED");
     
  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATASEQWRAP8 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap8Burst)
    $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA IN SEQ STATE FOR WRAP8 BURST : COVERED");

  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATASEQWRAP8 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap8Burst)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA IN SEQ STATE FOR WRAP8 BURST : COVERED");
      
  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATASEQINCR8 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement8Burst)
    $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA IN SEQ STATE FOR INCR8 BURST : COVERED");
    
  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATASEQINCR8 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement8Burst)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA IN SEQ STATE FOR INCR8 BURST : COVERED");
      
  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATASEQWRAP16 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateWrap16Burst)
    $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA IN SEQ STATE FOR WRAP16 BURST : COVERED");

  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATASEQWRAP16 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateWrap16Burst)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA IN SEQ STATE FOR WRAP16 BURST : COVERED");
          
  IFWRITEADDRANDDATAISEQUATOREADADDRANDDATASEQINCR16 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsSameInSeqStateIncrement16Burst)
    $info("WRITE ADDRESS AND DATA IS EQUAL TO MASTER READ ADDRESS AND DATA IN SEQ STATE FOR INCR16 BURST : COVERED");

  IFWRITEADDRANDDATAISNOTEQUALTOMASTERREADADDRANDDATASEQINCR16 : cover property
    (WriteDataIsEqualToReadDataAndBothTheAddressIsNotSameInSeqStateIncrement16Burst)
    $info("WRITE ADDRESS AND DATA IS NOT EQUAL TO READ ADDRESS AND DATA IN SEQ STATE FOR INCR16 BURST : COVERED");
     
endinterface : AhbCoverProperty

`endif
