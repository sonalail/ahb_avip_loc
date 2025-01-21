`ifndef AHBMASTERAGENTBFM_INCLUDED_
`define AHBMASTERAGENTBFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module      : AHB Master Agent BFM
// Description : Instantiates driver and monitor for AHB interface
//--------------------------------------------------------------------------------------------
module AhbMasterAgentBFM(AhbInterface intf); // Change interface to AhbInterface

  //-------------------------------------------------------
  // Importing uvm package file
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  initial begin
    `uvm_info("ahb master agent bfm", $sformatf("AHB MASTER AGENT BFM"), UVM_LOW);
  end
  
  //-------------------------------------------------------
  // master driver bfm instantiation
  //-------------------------------------------------------
  AhbMasterDriverBFM ahbMasterDriverBFM (
    .HCLK(intf.HCLK),
    .HRESETn(intf.HRESETn),
    .HADDR(intf.HADDR),
    .HBURST(intf.HBURST),
    .HMASTLOCK(intf.HMASTLOCK),
    .HPROT(intf.HPROT),
    .HSIZE(intf.HSIZE),
    .HNONSEC(intf.HNONSEC),
    .HEXCL(intf.HEXCL),
    .HMASTER(intf.HMASTER),
    .HTRANS(intf.HTRANS),
    .HWDATA(intf.HWDATA),
    .HWSTRB(intf.HWSTRB),
    .HWRITE(intf.HWRITE),
    .HRDATA(intf.HRDATA),
    .HREADYOUT(intf.HREADYOUT),
    .HRESP(intf.HRESP),
    .HEXOKAY(intf.HEXOKAY),
    .HREADY(intf.HREADY),
    .HSELx(intf.HSELx)
  );

  //-------------------------------------------------------
  // master monitor bfm instantiation
  //-------------------------------------------------------
  AhbMasterMonitorBFM ahbMasterMonitorBFM (
    .HCLK(intf.HCLK),
    .HRESETn(intf.HRESETn),
    .HADDR(intf.HADDR),
    .HBURST(intf.HBURST),
    .HMASTLOCK(intf.HMASTLOCK),
    .HPROT(intf.HPROT),
    .HSIZE(intf.HSIZE),
    .HNONSEC(intf.HNONSEC),
    .HEXCL(intf.HEXCL),
    .HMASTER(intf.HMASTER),
    .HTRANS(intf.HTRANS),
    .HWDATA(intf.HWDATA),
    .HWSTRB(intf.HWSTRB),
    .HWRITE(intf.HWRITE),
    .HRDATA(intf.HRDATA),
    .HREADYOUT(intf.HREADYOUT),
    .HRESP(intf.HRESP),
    .HEXOKAY(intf.HEXOKAY),
    .HREADY(intf.HREADY),
    .HSELx(intf.HSELx)
  );

  //-------------------------------------------------------
  // setting the virtual handle of BFMs into config_db
  //-------------------------------------------------------
  initial begin
    uvm_config_db#(virtual AhbMasterDriverBFM)::set(null,"*","AhbMasterDriverBFM", ahbMasterDriverBFM);
    uvm_config_db#(virtual AhbMasterMonitorBFM)::set(null,"*","AhbMasterMonitorBFM", ahbMasterMonitorBFM);
  end

endmodule : AhbMasterAgentBFM
`endif
