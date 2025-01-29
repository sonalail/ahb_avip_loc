`ifndef AHBSLAVEAGENTBFM_INCLUDED_
`define AHBSLAVEAGENTBFM_INCLUDED_

module AhbSlaveAgentBFM #(parameter int SLAVE_ID=0) (AhbInterface ahbInterface);

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  initial begin
    `uvm_info("ahb slave agent bfm",$sformatf("AHB SLAVE AGENT BFM"),UVM_LOW);
  end
 
  AhbSlaveDriverBFM ahbSlaveDriverBFM(.hclk(ahbInterface.hclk),
                                           .hresetn(ahbInterface.hresetn),
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
                                           .hready(ahbInterface.hready),
                                           .hselx(ahbInterface.hselx)
                                          );

  AhbSlaveMonitorBFM ahbSlaveMonitorBFM(.hclk(ahbInterface.hclk),
                                           .hresetn(ahbInterface.hresetn),
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
                                           .hready(ahbInterface.hready),
                                           .hselx(ahbInterface.hselx)
                                          );
  initial begin
    uvm_config_db#(virtual AhbSlaveDriverBFM)::set(null,"*", "AhbSlaveDriverBFM", ahbSlaveDriverBFM); 
    uvm_config_db #(virtual AhbSlaveMonitorBFM)::set(null,"*", "AhbSlaveMonitorBFM", ahbSlaveMonitorBFM); 
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("hselx=%0d",ahbInterface.hselx),UVM_HIGH)
    `uvm_info("SLAVE_AGENT_BFM",$sformatf("hselx=%0d",SLAVE_ID),UVM_HIGH)
  end

  // Bind AHB Slave Assertions to the Monitor BFM
  bind AhbSlaveMonitorBFM ahbSlaveAssertions ahb_assert (.hclk(ahbInterface.hclk),
                                                         .hresetn(ahbInterface.hresetn),
                                                         .hreadyout(ahbInterface.hreadyout),
                                                         .hrdata(ahbInterface.hrdata),
                                                         .hresp(ahbInterface.hresp),
                                                         .haddr(ahbInterface.haddr),
                                                         .htrans(ahbInterface.htrans),
                                                         .hwrite(ahbInterface.hwrite),
                                                         .hsize(ahbInterface.hsize),
                                                         .hburst(ahbInterface.hburst),
                                                         .hselx(ahbInterface.hselx),
                                                         .hwdata(ahbInterface.hwdata),
                                                         .hprot(ahbInterface.hprot),
                                                         .hexokay(ahbInterface.hexokay),
                                                         .hstrb(ahbInterface.hwstrb)
                                                        );


endmodule : AhbSlaveAgentBFM

`endif

