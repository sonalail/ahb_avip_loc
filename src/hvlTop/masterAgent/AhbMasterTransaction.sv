
`ifndef AHBMASTERTRANSACTION_INCLUDED_
`define AHBMASTERTRANSACTION_INCLUDED_

 class AhbMasterTransaction extends uvm_sequence_item;
  `uvm_object_utils(AhbMasterTransaction)

  rand bit [ADDR_WIDTH-1:0] haddr;
  rand bit [NO_OF_SLAVES-1:0] hselx;
  rand ahbBurstEnum hburst;
  rand bit hmastlock;
  rand ahbProtectionEnum hprot;
  rand ahbHsizeEnum hsize;
  rand bit hnonsec;
  rand bit hexcl;
  rand bit [HMASTER_WIDTH-1:0] hmaster;
  rand ahbTransferEnum htrans;
  rand bit [DATA_WIDTH-1:0] hwdata;
  rand bit [(DATA_WIDTH/8)-1:0] hwstrb;
  rand bit hwrite;
  bit [DATA_WIDTH-1:0] hrdata;
  bit hreadyout;
  ahbRespEnum hresp;
 // ahbRespEnum hexokay;
  bit hready;
  extern function new  (string name = "AhbMasterTransaction");
  extern function void do_copy(uvm_object rhs);
  extern function bit  do_compare(uvm_object rhs, uvm_comparer comparer);
  extern function void do_print(uvm_printer printer);
  
constraint addr_size {
    soft haddr > 0;
    if (hburst == SINGLE) soft haddr == 1;
    if (hburst == INCR) soft haddr < (1024 / (2 ** hsize));
    if (hburst == INCR4 || hburst == WRAP4) soft haddr == 4;
    if (hburst == INCR8 || hburst == WRAP8) soft haddr== 8;
    if (hburst == INCR16 || hburst == WRAP16) soft haddr== 16;
}

constraint wdata {
    soft hwdata == hsize;
}

constraint trans_size {
    soft htrans== haddr;
}

constraint first_trans_type {
    if (hburst == SINGLE) {
        soft htrans inside {IDLE, NONSEQ};
    } else {
        soft htrans == NONSEQ;
    }
}

constraint incr_trans_type {
    if (hburst != SINGLE) {
        if (htrans == IDLE)
            soft htrans == NONSEQ;
        else
            soft htrans == SEQ;
    }
}


constraint trans_val {
    soft hsize <= DATA_WIDTH;
}

constraint addr_boundary {
    if (hsize == HALFWORD)
        soft haddr[0] == 0;
    if (hsize == WORD)
        soft haddr[1:0] == 0;
    if (hsize == DOUBLEWORD)
        soft haddr[2:0] == 0;
    if (hsize == LINE4)
        soft haddr[3:0] == 0;
    if (hsize == LINE8)
        soft haddr[4:0] == 0;
    if (hsize == LINE16)
        soft haddr[5:0] == 0;
    if (hsize == LINE32)
        soft haddr[6:0] == 0;
}

constraint addr_vals {
    if (hburst inside {INCR, INCR4, INCR8, INCR16}) {
        soft haddr == haddr + 2**hsize; // Increment haddr based on hsize
    }
}


constraint addr_4beat_wrap {
    if (hburst == WRAP4) {
        if (hsize == BYTE)
            soft haddr[1:0] == haddr[1:0] + 1;
            soft haddr[ADDR_WIDTH-1:2] == haddr[ADDR_WIDTH-1:2];
        if (hsize == HALFWORD)
            soft haddr[2:1] == haddr[2:1] + 1;
            soft haddr[ADDR_WIDTH-1:3] == haddr[ADDR_WIDTH-1:3];
        if (hsize == WORD)
            soft haddr[3:2] == haddr[3:2] + 1;
            soft haddr[ADDR_WIDTH-1:4] == haddr[ADDR_WIDTH-1:4];
 }
}


constraint addr_8beat_wrap {
    if (hburst == WRAP8) {
        if (hsize == BYTE)
            soft haddr[2:0] == haddr[2:0] + 1;
            soft haddr[ADDR_WIDTH-1:3] == haddr[ADDR_WIDTH-1:3];
        if (hsize == HALFWORD)
            soft haddr[3:1] == haddr[3:1] + 1;
            soft haddr[ADDR_WIDTH-1:4] == haddr[ADDR_WIDTH-1:4];
        if (hsize == WORD)
            soft haddr[4:2] == haddr[4:2] + 1;
            soft haddr[ADDR_WIDTH-1:5] == haddr[ADDR_WIDTH-1:5];
}    
}


endclass : AhbMasterTransaction

function AhbMasterTransaction::new(string name = "AhbMasterTransaction");
  super.new(name);
endfunction : new

function void AhbMasterTransaction::do_copy (uvm_object rhs);
 AhbMasterTransaction ahbMasterTransaction;

  if(!$cast(ahbMasterTransaction,rhs)) begin
    `uvm_fatal("do_copy","cast of the rhs object failed")
  end
  super.do_copy(rhs);

haddr      = ahbMasterTransaction.haddr;
hselx      = ahbMasterTransaction.hselx;
hburst     = ahbMasterTransaction.hburst;
hmastlock  = ahbMasterTransaction.hmastlock;
hprot      = ahbMasterTransaction.hprot;
hsize      = ahbMasterTransaction.hsize;
hnonsec    = ahbMasterTransaction.hnonsec;
hexcl      = ahbMasterTransaction.hexcl;
hmaster    = ahbMasterTransaction.hmaster;
htrans     = ahbMasterTransaction.htrans;
hwdata     = ahbMasterTransaction.hwdata;
hwstrb     = ahbMasterTransaction.hwstrb;
hwrite     = ahbMasterTransaction.hwrite;
hrdata     = ahbMasterTransaction.hrdata;
hreadyout  = ahbMasterTransaction.hreadyout;
hresp      = ahbMasterTransaction.hresp;
//hexokay    = ahbMasterTransaction.hexokay;
hready     = ahbMasterTransaction.hready;

endfunction : do_copy

function bit AhbMasterTransaction::do_compare (uvm_object rhs, uvm_comparer comparer);
  AhbMasterTransaction ahbMasterTransaction;

 if(!$cast(ahbMasterTransaction,rhs)) begin
  `uvm_fatal("FATAL_AHB_MASTER_TX_DO_COMPARE_FAILED","cast of the rhs object failed")
    return 0;
  end

 return super.do_compare(ahbMasterTransaction, comparer) &&
haddr    == ahbMasterTransaction.haddr    &&
hselx    == ahbMasterTransaction.hselx    &&
hburst   == ahbMasterTransaction.hburst   &&
hmastlock == ahbMasterTransaction.hmastlock &&
hprot    == ahbMasterTransaction.hprot    &&
hsize    == ahbMasterTransaction.hsize    &&
hnonsec  == ahbMasterTransaction.hnonsec  &&
hexcl    == ahbMasterTransaction.hexcl    &&
hmaster  == ahbMasterTransaction.hmaster  &&
htrans   == ahbMasterTransaction.htrans   &&
hwdata   == ahbMasterTransaction.hwdata   &&
hwstrb   == ahbMasterTransaction.hwstrb   &&
hwrite   == ahbMasterTransaction.hwrite   &&
hrdata   == ahbMasterTransaction.hrdata   &&
hreadyout == ahbMasterTransaction.hreadyout &&
hresp    == ahbMasterTransaction.hresp    &&
//hexokay  == ahbMasterTransaction.hexokay  &&
hready   == ahbMasterTransaction.hready;

endfunction : do_compare
function void AhbMasterTransaction::do_print(uvm_printer printer);

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
//printer.print_string ("hexokay", hexokay.name());
printer.print_field ("hready", hready, $bits(hready), UVM_HEX);

endfunction : do_print

`endif


