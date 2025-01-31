`ifndef AHBSLAVETRANSACTION_INCLUDED_
`define AHBSLAVETRANSACTION_INCLUDED_

class AhbSlaveTransaction extends uvm_sequence_item;
  `uvm_object_utils(AhbSlaveTransaction)

bit [ADDR_WIDTH-1:0] haddr;
bit [NO_OF_SLAVES-1:0] hselx;
ahbBurstEnum hburst;
bit hmastlock;
ahbProtectionEnum hprot;
ahbHsizeEnum hsize;
bit hnonsec;
bit hexcl;
bit [HMASTER_WIDTH-1:0] hmaster;
ahbTransferEnum htrans;
bit [DATA_WIDTH-1:0] hwdata;
bit [(DATA_WIDTH/8)-1:0] hwstrb;
bit hwrite;
rand bit [DATA_WIDTH-1:0] hrdata;
rand bit hreadyout;
rand ahbRespEnum hresp;
 rand bit hexokay;
 rand bit hready;
 
  extern function new(string name = "AhbSlaveTransaction");
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
  extern function void do_print(uvm_printer printer);

  constraint c_hreadyout_timing {
    if (hready == 1) {
      hreadyout == 1;
  }
}

constraint c_hresp_valid {
  if (hreadyout == 1) {
    hresp == OKAY;
  }
}


constraint c_hexokay_valid {
  if (hexcl == 1) {
    hexokay == OKAY;
  } else {
    hexokay == 0;
  }
  if (hresp == ERROR) {
    hexokay == 0;
  }
}

task applyHreadyoutDelay();
        if (hresp == ERROR) begin
            #1;  
            hreadyout = 1;
        end
    endtask

endclass : AhbSlaveTransaction

function AhbSlaveTransaction::new(string name = "AhbSlaveTransaction");
  super.new(name);
endfunction : new

function void AhbSlaveTransaction::do_copy(uvm_object rhs);
  AhbSlaveTransaction ahbSlaveTransaction;

  if (!$cast(ahbSlaveTransaction, rhs)) begin
    `uvm_fatal("do_copy", "cast of the rhs object failed")
  end
  super.do_copy(rhs);

haddr     = ahbSlaveTransaction.haddr;
hselx     = ahbSlaveTransaction.hselx;
hburst    = ahbSlaveTransaction.hburst;
hmastlock = ahbSlaveTransaction.hmastlock;
hprot     = ahbSlaveTransaction.hprot;
hsize     = ahbSlaveTransaction.hsize;
hnonsec   = ahbSlaveTransaction.hnonsec;
hexcl     = ahbSlaveTransaction.hexcl;
hmaster   = ahbSlaveTransaction.hmaster;
htrans    = ahbSlaveTransaction.htrans;
hwdata   = ahbSlaveTransaction.hwdata;
hwstrb    = ahbSlaveTransaction.hwstrb;
hwrite    = ahbSlaveTransaction.hwrite;
hrdata    = ahbSlaveTransaction.hrdata;
hreadyout = ahbSlaveTransaction.hreadyout;
hresp     = ahbSlaveTransaction.hresp;
hexokay   = ahbSlaveTransaction.hexokay;
hready    = ahbSlaveTransaction.hready;

endfunction : do_copy

function bit AhbSlaveTransaction::do_compare(uvm_object rhs, uvm_comparer comparer);
  AhbSlaveTransaction ahbSlaveTransaction;

  if (!$cast(ahbSlaveTransaction, rhs)) begin
    `uvm_fatal("FATAL_AHB_SLAVE_TX_DO_COMPARE_FAILED", "cast of the rhs object failed")
    return 0;
  end

return super.do_compare(ahbSlaveTransaction, comparer) &&
haddr     == ahbSlaveTransaction.haddr     &&
hselx     == ahbSlaveTransaction.hselx     &&
hburst    == ahbSlaveTransaction.hburst    &&
hmastlock == ahbSlaveTransaction.hmastlock &&
hprot     == ahbSlaveTransaction.hprot     &&
hsize     == ahbSlaveTransaction.hsize     &&
hnonsec   == ahbSlaveTransaction.hnonsec   &&
hexcl     == ahbSlaveTransaction.hexcl     &&
hmaster   == ahbSlaveTransaction.hmaster   &&
htrans    == ahbSlaveTransaction.htrans    &&
hwdata   == ahbSlaveTransaction.hwdata     &&
hwstrb    == ahbSlaveTransaction.hwstrb    &&
hwrite    == ahbSlaveTransaction.hwrite    &&
hrdata    == ahbSlaveTransaction.hrdata    &&
hreadyout == ahbSlaveTransaction.hreadyout &&
hresp     == ahbSlaveTransaction.hresp     &&
hexokay   == ahbSlaveTransaction.hexokay   &&
hready    == ahbSlaveTransaction.hready;
endfunction : do_compare

function void AhbSlaveTransaction::do_print(uvm_printer printer);
printer.print_field  ("haddr", haddr, $bits(haddr), UVM_HEX);
printer.print_field  ("hselx", hselx, $bits(hselx), UVM_BIN);
printer.print_string ("hburst", hburst.name());
printer.print_field ("hmastlock", hmastlock, $bits(hmastlock), UVM_HEX);
printer.print_string ("hprot", hprot.name());
printer.print_string ("hsize", hsize.name());
printer.print_field ("hnonsec", hnonsec, $bits(hnonsec), UVM_HEX);
printer.print_field ("hexcl", hexcl, $bits(hexcl), UVM_HEX);
printer.print_field  ("hmaster", hmaster, $bits(hmaster), UVM_DEC);
printer.print_string ("htrans", htrans.name());
printer.print_field  ("hwdata", hwdata, $bits(hwdata), UVM_HEX);
printer.print_field  ("hwstrb", hwstrb, $bits(hwstrb), UVM_BIN);
printer.print_field ("hwrite", hwrite, $bits(hwrite), UVM_BIN);
printer.print_field  ("hrdata", hrdata, $bits(hrdata), UVM_HEX);
printer.print_field ("hreadyout", hreadyout, $bits(hreadyout), UVM_HEX);
printer.print_string ("hresp", hresp.name());
  printer.print_string ("hexokay",  hexokay, $bits(hexokay), UVM_HEX);
printer.print_field ("hready", hready, $bits(hready), UVM_HEX);
endfunction : do_print

`endif
