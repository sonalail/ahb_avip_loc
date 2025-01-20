`ifndef AHB_MASTER_AGENT_BFM_INCLUDED_
`define AHB_MASTER_AGENT_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module      : AHB Master Agent BFM
// Description : Instantiates driver and monitor for AHB interface
//--------------------------------------------------------------------------------------------
module AhbMasterAgentBfm(AhbInterface intf); // Change interface to ahb_if

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
  AhbMasterDriverBfm ahb_master_drv_bfm_h (
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
  AhbMasterMonitorBfm ahb_master_mon_bfm_h (
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
    uvm_config_db#(virtual AhbMasterDriverBfm)::set(null,"*","AhbMasterDriverBfm", ahb_master_drv_bfm_h);
    uvm_config_db#(virtual AhbMasterMonitorBfm)::set(null,"*","AhbMasterMonitorBfm", ahb_master_mon_bfm_h);
  end

endmodule : AhbMasterAgentBfm
`endif
