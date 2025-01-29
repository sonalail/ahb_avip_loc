`ifndef AHBMASTERAGENTBFM_INCLUDED_
`define AHBMASTERAGENTBFM_INCLUDED_

module AhbMasterAgentBFM(AhbInterface ahbInterface); 

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  initial begin
    `uvm_info("ahb master agent bfm", $sformatf("AHB MASTER AGENT BFM"), UVM_LOW);
  end

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

  initial begin
    uvm_config_db#(virtual AhbMasterDriverBFM)::set(null,"*","AhbMasterDriverBFM", ahbMasterDriverBFM);
    uvm_config_db#(virtual AhbMasterMonitorBFM)::set(null,"*","AhbMasterMonitorBFM", ahbMasterMonitorBFM);
  end

bind AhbMasterMonitorBFM AhbMasterAssertions ahb_assert (.hclk(ahbInterface.hclk),
                                                         .hresetn(ahbInterface.hresetn),
                                                         .hready(ahbInterface.hready),
                                                         .haddr(ahbInterface.haddr),
                                                         .htrans(ahbInterface.htrans),
                                                         .hwrite(ahbInterface.hwrite),
                                                         .hsize(ahbInterface.hsize),
                                                         .hburst(ahbInterface.hburst),
                                                         .hprot(ahbInterface.hprot),
                                                         .hmaster(ahbInterface.hmaster),
                                                         .hmastlock(ahbInterface.hmastlock),
                                                         .hwdata(ahbInterface.hwdata),
                                                         .hresp(ahbInterface.hresp),
                                                         .hexcl(ahbInterface.hexcl),
                                                         .hwdata_valid(ahbInterface.hwdata_valid),
                                                         .htrans_valid(ahbInterface.htrans_valid)
                                                        );

endmodule : AhbMasterAgentBFM
`endif
