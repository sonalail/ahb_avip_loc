`ifndef AHBSLAVESEQUENCEITEMCONVERTER_INCLUDED_
`define AHBSLAVESEQUENCEITEMCONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class : AhbSlaveSequenceItemConverter
//  This class converts seq_item transactions into struct data items and vice versa
//--------------------------------------------------------------------------------------------
class AhbSlaveSequenceItemConverter extends uvm_object;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveSequenceItemConverter");
  extern static function void fromClass(input AhbSlaveTransaction ahbSlaveTransaction, output ahbTransferCharStruct outputConv);
  extern static function void toClass(input ahbTransferCharStruct inputConv, ref AhbSlaveTransaction outputConv);
  extern function void do_print(uvm_printer printer);

endclass : AhbSlaveSequenceItemConverter

//-------------------------------------------------------
// Construct:new
// 
// Parameters:
//  name - AhbSlaveSequenceItemConverter
//-------------------------------------------------------
function AhbSlaveSequenceItemConverter::new(string name = "AhbSlaveSequenceItemConverter");
  super.new(name);
endfunction: new

//--------------------------------------------------------------------------------------------
// Function: fromClass
//  Converting seq_item transactions into struct data items
//
// Parameters:
//  name - AhbSlaveTransaction, ahbTransferCharStruct
//--------------------------------------------------------------------------------------------
    function void AhbSlaveSequenceItemConverter::fromClass(input AhbSlaveTransaction ahbSlaveTransaction, output ahbTransferCharStruct outputConv);
  `uvm_info("AhbSlaveSeqItemConvClass",$sformatf("-------------------------------------------------------------"),UVM_HIGH);

      $cast(outputConv.HPROT, ahbSlaveTransaction.HPROT);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HPROT = %b", outputConv.HPROT), UVM_HIGH);

      $cast(outputConv.HBURST, ahbSlaveTransaction.HBURST);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HBURST = %b", outputConv.HBURST), UVM_HIGH);

  outputConv.HMASTLOCK = ahbSlaveTransaction.HMASTLOCK;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", outputConv.HMASTLOCK), UVM_HIGH);

      $cast(outputConv.HSIZE, ahbSlaveTransaction.HSIZE);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", outputConv.HSIZE), UVM_HIGH);

  outputConv.HNONSEC = ahbSlaveTransaction.HNONSEC;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", outputConv.HNONSEC), UVM_HIGH);

  outputConv.HEXCL = ahbSlaveTransaction.HEXCL;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", outputConv.HEXCL), UVM_HIGH);

      $cast(outputConv.HMASTER, ahbSlaveTransaction.HMASTER);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", outputConv.HMASTER), UVM_HIGH);

      $cast(outputConv.HTRANS, ahbSlaveTransaction.HTRANS);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", outputConv.HTRANS), UVM_HIGH);

  outputConv.HWDATA = ahbSlaveTransaction.HWDATA;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", outputConv.HWDATA), UVM_HIGH);

  outputConv.HWSTRB = ahbSlaveTransaction.HWSTRB;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", outputConv.HWSTRB), UVM_HIGH);

  outputConv.HWRITE = ahbSlaveTransaction.HWRITE;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", outputConv.HWRITE), UVM_HIGH);

  outputConv.HRDATA = ahbSlaveTransaction.HRDATA;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", outputConv.HRDATA), UVM_HIGH);

  outputConv.HREADYOUT = ahbSlaveTransaction.HREADYOUT;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", outputConv.HREADYOUT), UVM_HIGH);

      $cast(outputConv.HRESP, ahbSlaveTransaction.HRESP);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRESP = %b", outputConv.HRESP), UVM_HIGH);

  outputConv.HEXOKAY = ahbSlaveTransaction.HEXOKAY;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", outputConv.HEXOKAY), UVM_HIGH);

  outputConv.HREADY = ahbSlaveTransaction.HREADY;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADY = %b", outputConv.HREADY), UVM_HIGH);

  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : fromClass 

//--------------------------------------------------------------------------------------------
// Function: toClass
// Converting struct data items into seq_item transactions
//
// Parameters:
// name - AhbSlaveTransaction, ahbTransferCharStruct
//--------------------------------------------------------------------------------------------
    function void AhbSlaveSequenceItemConverter::toClass(input ahbTransferCharStruct inputConv, ref AhbSlaveTransaction ahbSlaveTransaction);
  `uvm_info("AhbSlaveSeqItemConv", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

      $cast(ahbSlaveTransaction.HPROT, inputConv.HPROT);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HPROT = %b", ahbSlaveTransaction.HPROT), UVM_HIGH);

      $cast(ahbSlaveTransaction.HBURST, inputConv.HBURST);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HBURST = %b", ahbSlaveTransaction.HBURST), UVM_HIGH);

  ahbSlaveTransaction.HMASTLOCK = inputConv.HMASTLOCK;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", ahbSlaveTransaction.HMASTLOCK), UVM_HIGH);

      $cast(ahbSlaveTransaction.HSIZE, inputConv.HSIZE);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", ahbSlaveTransaction.HSIZE), UVM_HIGH);

  ahbSlaveTransaction.HNONSEC = inputConv.HNONSEC;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", ahbSlaveTransaction.HNONSEC), UVM_HIGH);

  ahbSlaveTransaction.HEXCL = inputConv.HEXCL;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", ahbSlaveTransaction.HEXCL), UVM_HIGH);

      $cast(ahbSlaveTransaction.HMASTER, inputConv.HMASTER);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", ahbSlaveTransaction.HMASTER), UVM_HIGH);

      $cast(ahbSlaveTransaction.HTRANS, inputConv.HTRANS);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", ahbSlaveTransaction.HTRANS), UVM_HIGH);

  ahbSlaveTransaction.HWDATA = inputConv.HWDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", ahbSlaveTransaction.HWDATA), UVM_HIGH);

  ahbSlaveTransaction.HWSTRB = inputConv.HWSTRB;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", ahbSlaveTransaction.HWSTRB), UVM_HIGH);

  ahbSlaveTransaction.HWRITE = inputConv.HWRITE;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", ahbSlaveTransaction.HWRITE), UVM_HIGH);

  ahbSlaveTransaction.HRDATA = inputConv.HRDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", ahbSlaveTransaction.HRDATA), UVM_HIGH);

  ahbSlaveTransaction.HREADYOUT = inputConv.HREADYOUT;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", ahbSlaveTransaction.HREADYOUT), UVM_HIGH);

      $cast(ahbSlaveTransaction.HRESP, inputConv.HRESP);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRESP = %b", ahbSlaveTransaction.HRESP), UVM_HIGH);

  ahbSlaveTransaction.HEXOKAY = inputConv.HEXOKAY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", ahbSlaveTransaction.HEXOKAY), UVM_HIGH);

  ahbSlaveTransaction.HREADY = inputConv.HREADY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADY = %b", ahbSlaveTransaction.HREADY), UVM_HIGH);

  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : toClass

//-------------------------------------------------------
// Function: do_print
//  This function is used to print the sequence item data from the AhbSlaveSequenceItemConverter class
//-------------------------------------------------------
function void AhbSlaveSequenceItemConverter::do_print(uvm_printer printer);
  ahbTransferCharStruct ahbSt;
  super.do_print(printer);

  printer.print_field("HPROT", ahbSt.HPROT, $bits(ahbSt.HPROT), UVM_BIN);
  printer.print_field("HBURST", ahbSt.HBURST, $bits(ahbSt.HBURST), UVM_BIN);
  printer.print_field("HMASTLOCK", ahbSt.HMASTLOCK, $bits(ahbSt.HMASTLOCK), UVM_BIN);
  printer.print_field("HSIZE", ahbSt.HSIZE, $bits(ahbSt.HSIZE), UVM_BIN);
  printer.print_field("HNONSEC", ahbSt.HNONSEC, $bits(ahbSt.HNONSEC), UVM_BIN);
  printer.print_field("HEXCL", ahbSt.HEXCL, $bits(ahbSt.HEXCL), UVM_BIN);
  printer.print_field("HMASTER", ahbSt.HMASTER, $bits(ahbSt.HMASTER), UVM_BIN);
  printer.print_field("HTRANS", ahbSt.HTRANS, $bits(ahbSt.HTRANS), UVM_BIN);
  printer.print_field("HWDATA", ahbSt.HWDATA, $bits(ahbSt.HWDATA), UVM_HEX);
  printer.print_field("HWSTRB", ahbSt.HWSTRB, $bits(ahbSt.HWSTRB), UVM_BIN);
  printer.print_field("HWRITE", ahbSt.HWRITE, $bits(ahbSt.HWRITE), UVM_BIN);
  printer.print_field("HRDATA", ahbSt.HRDATA, $bits(ahbSt.HRDATA), UVM_HEX);
  printer.print_field("HREADYOUT", ahbSt.HREADYOUT, $bits(ahbSt.HREADYOUT), UVM_BIN);
  printer.print_field("HRESP", ahbSt.HRESP, $bits(ahbSt.HRESP), UVM_BIN);
  printer.print_field("HEXOKAY", ahbSt.HEXOKAY, $bits(ahbSt.HEXOKAY), UVM_BIN);
  printer.print_field("HREADY", ahbSt.HREADY, $bits(ahbSt.HREADY), UVM_BIN);

endfunction : do_print


`endif : AHBSLAVESEQUENCEITEMCONVERTER_INCLUDED_
