`ifndef AHBMASTERAGENTBFM_INCLUDED_
`define AHBMASTERAGENTBFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module      : AHB Master Agent BFM
// Description : Instantiates driver and monitor for AHB interface
//--------------------------------------------------------------------------------------------
module AhbMasterAgentBFM(AhbInterface ahbInterface); // Change interface to AhbInterface

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
    .HCLK(ahbInterface.HCLK),
    .HRESETn(ahbInterface.HRESETn),
    .HADDR(ahbInterface.HADDR),
    .HBURST(ahbInterface.HBURST),
    .HMASTLOCK(ahbInterface.HMASTLOCK),
    .HPROT(ahbInterface.HPROT),
    .HSIZE(ahbInterface.HSIZE),
    .HNONSEC(ahbInterface.HNONSEC),
    .HEXCL(ahbInterface.HEXCL),
    .HMASTER(ahbInterface.HMASTER),
    .HTRANS(ahbInterface.HTRANS),
    .HWDATA(ahbInterface.HWDATA),
    .HWSTRB(ahbInterface.HWSTRB),
    .HWRITE(ahbInterface.HWRITE),
    .HRDATA(ahbInterface.HRDATA),
    .HREADYOUT(ahbInterface.HREADYOUT),
    .HRESP(ahbInterface.HRESP),
    .HEXOKAY(ahbInterface.HEXOKAY),
    .HREADY(ahbInterface.HREADY),
    .HSELx(ahbInterface.HSELx)
  );

  //-------------------------------------------------------
  // master monitor bfm instantiation
  //-------------------------------------------------------
  AhbMasterMonitorBFM ahbMasterMonitorBFM (
    .HCLK(ahbInterface.HCLK),
    .HRESETn(ahbInterface.HRESETn),
    .HADDR(ahbInterface.HADDR),
    .HBURST(ahbInterface.HBURST),
    .HMASTLOCK(ahbInterface.HMASTLOCK),
    .HPROT(ahbInterface.HPROT),
    .HSIZE(ahbInterface.HSIZE),
    .HNONSEC(ahbInterface.HNONSEC),
    .HEXCL(ahbInterface.HEXCL),
    .HMASTER(ahbInterface.HMASTER),
    .HTRANS(ahbInterface.HTRANS),
    .HWDATA(ahbInterface.HWDATA),
    .HWSTRB(ahbInterface.HWSTRB),
    .HWRITE(ahbInterface.HWRITE),
    .HRDATA(ahbInterface.HRDATA),
    .HREADYOUT(ahbInterface.HREADYOUT),
    .HRESP(ahbInterface.HRESP),
    .HEXOKAY(ahbInterface.HEXOKAY),
    .HREADY(ahbInterface.HREADY),
    .HSELx(ahbInterface.HSELx)
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
