`ifndef AHBSLAVEAGENTBFM_INCLUDED_
`define AHBSLAVEAGENTBFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module      : AhbSlaveAgentBFM
// Description : Instantiates driver and monitor
//--------------------------------------------------------------------------------------------
module AhbSlaveAgentBFM #(parameter int SLAVE_ID=0) (AhbInterface ahbInterface);

  //-------------------------------------------------------
  // Importing uvm_pkg file
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  initial begin
    `uvm_info("ahb slave agent bfm",$sformatf("AHB SLAVE AGENT BFM"),UVM_LOW);
  end
  
  //-------------------------------------------------------
  // slave driver bfm instantiation
  //-------------------------------------------------------
  AhbSlaveDriverBFM ahbSlaveDriverBFM(.HCLK(ahbInterface.HCLK),
                                           .HRESETn(ahbInterface.HRESETn),
                                           .HSELx(ahbInterface.HSELx),
                                           .HBURST(ahbInterface.HBURST),
                                           .HMASTLOCK(ahbInterface.HMASTLOCK),
                                           .HADDR(ahbInterface.HADDR),
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
                                          );


  //-------------------------------------------------------
  // slave monitor bfm instantiation
  //-------------------------------------------------------
  AhbSlaveMonitorBFM ahbSlaveMonitorBFM(.HCLK(ahbInterface.HCLK),
                                           .HRESETn(ahbInterface.HRESETn),
                                           .HSELx(ahbInterface.HSELx),
                                           .HBURST(ahbInterface.HBURST),
                                           .HMASTLOCK(ahbInterface.HMASTLOCK),
                                           .HADDR(ahbInterface.HADDR),
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
                                          );
  initial begin
    uvm_config_db#(virtual AhbSlaveDriverBFM)::set(null,"*", "ahb_slave_driver_bfm", ahbSlaveDriverBFM); 
    uvm_config_db #(virtual AhbSlaveMonitorBFM)::set(null,"*", "ahb_slave_monitor_bfm", ahbSlaveMonitorBFM); 
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("HSELx=%0d",intf.HSELx),UVM_HIGH)
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("HSELx=%0d",SLAVE_ID),UVM_HIGH)
  end

endmodule : AhbSlaveAgentBFM

`endif

