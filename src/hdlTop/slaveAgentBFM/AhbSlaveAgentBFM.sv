`ifndef AHBSLAVEAGENTBFM_INCLUDED_
`define AHBSLAVEAGENTBFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module      : AhbSlaveAgentBFM
// Description : Instantiates driver and monitor
//--------------------------------------------------------------------------------------------
module AhbSlaveAgentBFM #(parameter int SLAVE_ID=0) (AhbInterface intf);

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
  AhbSlaveDriverBFM ahbSlaveDriverBFM(.HCLK(intf.HCLK),
                                           .HRESETn(intf.HRESETn),
                                           .HSELx(intf.HSELx),
                                           .HBURST(intf.HBURST),
                                           .HMASTLOCK(intf.HMASTLOCK),
                                           .HADDR(intf.HADDR),
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
                                          );


  //-------------------------------------------------------
  // slave monitor bfm instantiation
  //-------------------------------------------------------
  AhbSlaveMonitorBFM ahbSlaveMonitorBFM(.HCLK(intf.HCLK),
                                           .HRESETn(intf.HRESETn),
                                           .HSELx(intf.HSELx),
                                           .HBURST(intf.HBURST),
                                           .HMASTLOCK(intf.HMASTLOCK),
                                           .HADDR(intf.HADDR),
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
                                          );
  initial begin
    uvm_config_db#(virtual AhbSlaveDriverBFM)::set(null,"*", "ahb_slave_driver_bfm", ahbSlaveDriverBFM); 
    uvm_config_db #(virtual AhbSlaveMonitorBFM)::set(null,"*", "ahb_slave_monitor_bfm", ahbSlaveMonitorBFM); 
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("HSELx=%0d",intf.HSELx),UVM_HIGH)
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("HSELx=%0d",SLAVE_ID),UVM_HIGH)
  end

endmodule : AhbSlaveAgentBFM

`endif

