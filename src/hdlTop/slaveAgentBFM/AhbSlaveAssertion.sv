`ifndef AHBSLAVEASSERTION_INCLUDED_
`define AHBSLAVEASSERTION_INCLUDED_

import AhbGlobalPackage::*;

interface AhbSlaveAssertion (
  input   	         hclk,          
  input        		 hresetn,       
  input        		 hreadyout,    
  input [DATA_WIDTH-1:0] hrdata,       
  input   		 hresp,         
  input [ADDR_WIDTH-1:0] haddr,    
  input 	   [1:0] htrans,       
  input      		 hwrite,        
  input 	   [2:0] hsize,        
  input 	   [2:0] hburst,        
  input       		 hselx,     
  input 	  [31:0] hwdata,        
  input            [3:0] hprot,         
  input      		 hexokay,       
  input 	   [3:0] hwstrb          
);


  property checkHreadyoutValid;
    @(posedge hclk) disable iff (!hresetn)
    hreadyout; 
  endproperty

  assert property (checkHreadyoutValid)
       $info("HREADYOUT is high during valid transactions!");
  else $error("HREADYOUT is not high during valid transactions!");

  property checkHrespErrorOnInvalid;
    @(posedge hclk) disable iff (!hresetn)
    (hreadyout && (htrans == 2'b00)) |-> (hresp == 1'b1);  
  endproperty

  assert property (checkHrespErrorOnInvalid)
       $info("HRESP is ERROR for valid transfers!");
  else $error("HRESP is not ERROR for invalid transfers!");


  property checkHrespOkayForValid;
    @(posedge hclk) disable iff (!hresetn)
    (hreadyout && (htrans != 2'b00)) |-> (hresp == 1'b0);  
  endproperty

  assert property (checkHrespOkayForValid)
       $info("HRESP is OKAY for valid transactions!");
  else $error("HRESP is not OKAY for valid transactions!");

  property checkSlaveHrdataValid;
    @(posedge hclk) disable iff (!hresetn)
    (!hwrite && hreadyout && (htrans != 2'b00)) |=> (!$isunknown(hrdata));  
  endproperty

  assert property (checkSlaveHrdataValid)
       $info("HRDATA is valid during read transfer!");
  else $error("HRDATA is invalid during read transfer!");

  property checkHaddrUnchanged;
    @(posedge hclk) disable iff (!hresetn)
    (hreadyout && (htrans != 2'b00)) |-> (haddr == $past(haddr));  
  endproperty

  assert property (checkHaddrUnchanged)
       $info("HADDR remains unchanged during a transfer!");
  else $error("HADDR changed unexpectedly during a transfer!");

  property checkHsizeMatchesData;
    @(posedge hclk) disable iff (!hresetn)
    (hreadyout && (htrans != 2'b00)) |-> ((1 << hsize) <= 32);  
  endproperty

  assert property (checkHsizeMatchesData)
       $info("HSIZE matches the data width supported by the slave!");
  else $error("HSIZE does not match the data width supported by the slave!");

  property checkBurstTypeValid;
    @(posedge hclk) disable iff (!hresetn)
    (hreadyout && (htrans != 2'b00)) |-> (hburst == 3'b000 || 
                                          hburst == 3'b001 || 
                                          hburst == 3'b010 || 
                                          hburst == 3'b011 || 
                                          hburst == 3'b100); 
  endproperty

  assert property (checkBurstTypeValid)
       $info("Valid burst type!");
  else $error("Invalid burst type detected!");

endinterface : AhbSlaveAssertion

`endif

