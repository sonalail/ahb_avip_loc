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
  AhbSlaveDriverBFM ahbSlaveDriverBFM(.hclk(ahbInterface.hclk),
                                           .hresetn(ahbInterface.hresetn),
                                           .hselx(ahbInterface.hselx),
                                           .hburst(ahbInterface.hburst),
                                           .hmastlock(ahbInterface.hmastlock),
                                           .haddr(ahbInterface.haddr),
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
                                           .hready(ahbInterface.hready)
                                          );


  //-------------------------------------------------------
  // slave monitor bfm instantiation
  //-------------------------------------------------------
  AhbSlaveMonitorBFM ahbSlaveMonitorBFM(.hclk(ahbInterface.hclk),
                                           .hresetn(ahbInterface.hresetn),
                                           .hselx(ahbInterface.hselx),
                                           .hburst(ahbInterface.hburst),
                                           .hmastlock(ahbInterface.hmastlock),
                                           .haddr(ahbInterface.haddr),
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
                                           .hready(ahbInterface.hready)
                                          );
  initial begin
    uvm_config_db#(virtual AhbSlaveDriverBFM)::set(null,"*", "AhbSlaveDriverBFM", ahbSlaveDriverBFM); 
    uvm_config_db #(virtual AhbSlaveMonitorBFM)::set(null,"*", "AhbSlaveMonitorBFM", ahbSlaveMonitorBFM); 
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("hselx=%0d",ahbInterface.hselx),UVM_HIGH)
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("hselx=%0d",SLAVE_ID),UVM_HIGH)
  end

endmodule : AhbSlaveAgentBFM

`endif

