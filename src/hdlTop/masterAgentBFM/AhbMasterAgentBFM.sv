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
    .hclk(ahbInterface.hclk),
    .hresetn(ahbInterface.hresetn),
    .haddr(ahbInterface.haddr),
    .hburst(ahbInterface.hburst),
    .hmastlock(ahbInterface.hmastlock),
    .hprot(ahbInterface.hprot),
    .hsize(ahbInterface.hsize),
    .hnonsec(ahbInterface.hnonsec),
    .hexcl(ahbInterface.hexcl),
    .hmaster(ahbInterface.hmaster),
    .htrans(ahbInterface.htrans),
    .hwdata(ahbInterface.hwdata),
    .hwstrb(ahbInterface.hwstrb),
    .hwrite(ahbInterface.hwrite),
    .hrdata(ahbInterface.hrdata),
    .hreadyout(ahbInterface.hreadyout),
    .hresp(ahbInterface.hresp),
    .hexokay(ahbInterface.hexokay),
    .hready(ahbInterface.hready),
    .hselx(ahbInterface.hselx)
  );

  //-------------------------------------------------------
  // master monitor bfm instantiation
  //-------------------------------------------------------
  AhbMasterMonitorBFM ahbMasterMonitorBFM (
    .hclk(ahbInterface.hclk),
    .hresetn(ahbInterface.hresetn),
    .haddr(ahbInterface.haddr),
    .hburst(ahbInterface.hburst),
    .hmastlock(ahbInterface.hmastlock),
    .hprot(ahbInterface.hprot),
    .hsize(ahbInterface.hsize),
    .hnonsec(ahbInterface.hnonsec),
    .hexcl(ahbInterface.hexcl),
    .hmaster(ahbInterface.hmaster),
    .htrans(ahbInterface.htrans),
    .hwdata(ahbInterface.hwdata),
    .hwstrb(ahbInterface.hwstrb),
    .hwrite(ahbInterface.hwrite),
    .hrdata(ahbInterface.hrdata),
    .hreadyout(ahbInterface.hreadyout),
    .hresp(ahbInterface.hresp),
    .hexokay(ahbInterface.hexokay),
    .hready(ahbInterface.hready),
    .hselx(ahbInterface.hselx)
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
