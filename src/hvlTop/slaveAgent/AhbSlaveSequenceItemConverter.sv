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
    extern static function void fromClass(input AhbSlaveTransaction inputConv, output ahbTransferCharStruct outputConv);
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
    function void AhbSlaveSequenceItemConverter::fromClass(input AhbSlaveTransaction inputConv, output ahbTransferCharStruct outputConv);
  `uvm_info("AhbSlaveSeqItemConvClass",$sformatf("-------------------------------------------------------------"),UVM_HIGH);

      $cast(outputConv.HPROT, inputConv.HPROT);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HPROT = %b", outputConv.HPROT), UVM_HIGH);

      $cast(outputConv.HBURST, inputConv.HBURST);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HBURST = %b", outputConv.HBURST), UVM_HIGH);

  outputConv.HMASTLOCK = inputConv.HMASTLOCK;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", outputConv.HMASTLOCK), UVM_HIGH);

      $cast(outputConv.HSIZE, inputConv.HSIZE);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", outputConv.HSIZE), UVM_HIGH);

  outputConv.HNONSEC = inputConv.HNONSEC;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", outputConv.HNONSEC), UVM_HIGH);

  outputConv.HEXCL = inputConv.HEXCL;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", outputConv.HEXCL), UVM_HIGH);

      $cast(outputConv.HMASTER, inputConv.HMASTER);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", outputConv.HMASTER), UVM_HIGH);

      $cast(outputConv.HTRANS, inputConv.HTRANS);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", outputConv.HTRANS), UVM_HIGH);

  outputConv.HWDATA = inputConv.HWDATA;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", outputConv.HWDATA), UVM_HIGH);

  outputConv.HWSTRB = inputConv.HWSTRB;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", outputConv.HWSTRB), UVM_HIGH);

  outputConv.HWRITE = inputConv.HWRITE;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", outputConv.HWRITE), UVM_HIGH);

  outputConv.HRDATA = inputConv.HRDATA;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", outputConv.HRDATA), UVM_HIGH);

  outputConv.HREADYOUT = inputConv.HREADYOUT;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", outputConv.HREADYOUT), UVM_HIGH);

      $cast(outputConv.HRESP, inputConv.HRESP);
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRESP = %b", outputConv.HRESP), UVM_HIGH);

  outputConv.HEXOKAY = inputConv.HEXOKAY;
      `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", outputConv.HEXOKAY), UVM_HIGH);

  outputConv.HREADY = inputConv.HREADY;
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
    function void AhbSlaveSequenceItemConverter::toClass(input ahbTransferCharStruct inputConv, ref AhbSlaveTransaction outputConv);
  `uvm_info("AhbSlaveSeqItemConv", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

      $cast(outputConv.HPROT, inputConv.HPROT);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HPROT = %b", outputConv.HPROT), UVM_HIGH);

      $cast(outputConv.HBURST, inputConv.HBURST);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HBURST = %b", outputConv.HBURST), UVM_HIGH);

  outputConv.HMASTLOCK = inputConv.HMASTLOCK;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", outputConv.HMASTLOCK), UVM_HIGH);

      $cast(outputConv.HSIZE, inputConv.HSIZE);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", outputConv.HSIZE), UVM_HIGH);

  outputConv.HNONSEC = inputConv.HNONSEC;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", outputConv.HNONSEC), UVM_HIGH);

  outputConv.HEXCL = inputConv.HEXCL;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", outputConv.HEXCL), UVM_HIGH);

      $cast(outputConv.HMASTER, inputConv.HMASTER);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", outputConv.HMASTER), UVM_HIGH);

      $cast(outputConv.HTRANS, inputConv.HTRANS);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", outputConv.HTRANS), UVM_HIGH);

  outputConv.HWDATA = inputConv.HWDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", outputConv.HWDATA), UVM_HIGH);

  outputConv.HWSTRB = inputConv.HWSTRB;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", outputConv.HWSTRB), UVM_HIGH);

  outputConv.HWRITE = inputConv.HWRITE;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", outputConv.HWRITE), UVM_HIGH);

  outputConv.HRDATA = inputConv.HRDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", outputConv.HRDATA), UVM_HIGH);

  outputConv.HREADYOUT = inputConv.HREADYOUT;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", outputConv.HREADYOUT), UVM_HIGH);

      $cast(outputConv.HRESP, inputConv.HRESP);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRESP = %b", outputConv.HRESP), UVM_HIGH);

  outputConv.HEXOKAY = inputConv.HEXOKAY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", outputConv.HEXOKAY), UVM_HIGH);

  outputConv.HREADY = inputConv.HREADY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADY = %b", outputConv.HREADY), UVM_HIGH);

  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : toClass

//-------------------------------------------------------
// Function: do_print
//  This function is used to print the sequence item data from the AhbSlaveSequenceItemConverter class
//-------------------------------------------------------
function void AhbSlaveSequenceItemConverter::do_print(uvm_printer printer);
  ahbTransferCharStruct ahbStruct;
  super.do_print(printer);

  printer.print_field("HPROT", ahbStruct.HPROT, $bits(ahbStruct.HPROT), UVM_BIN);
  printer.print_field("HBURST", ahbStruct.HBURST, $bits(ahbStruct.HBURST), UVM_BIN);
  printer.print_field("HMASTLOCK", ahbStruct.HMASTLOCK, $bits(ahbStruct.HMASTLOCK), UVM_BIN);
  printer.print_field("HSIZE", ahbStruct.HSIZE, $bits(ahbStruct.HSIZE), UVM_BIN);
  printer.print_field("HNONSEC", ahbStruct.HNONSEC, $bits(ahbStruct.HNONSEC), UVM_BIN);
  printer.print_field("HEXCL", ahbStruct.HEXCL, $bits(ahbStruct.HEXCL), UVM_BIN);
  printer.print_field("HMASTER", ahbStruct.HMASTER, $bits(ahbStruct.HMASTER), UVM_BIN);
  printer.print_field("HTRANS", ahbStruct.HTRANS, $bits(ahbStruct.HTRANS), UVM_BIN);
  printer.print_field("HWDATA", ahbStruct.HWDATA, $bits(ahbStruct.HWDATA), UVM_HEX);
  printer.print_field("HWSTRB", ahbStruct.HWSTRB, $bits(ahbStruct.HWSTRB), UVM_BIN);
  printer.print_field("HWRITE", ahbStruct.HWRITE, $bits(ahbStruct.HWRITE), UVM_BIN);
  printer.print_field("HRDATA", ahbStruct.HRDATA, $bits(ahbStruct.HRDATA), UVM_HEX);
  printer.print_field("HREADYOUT", ahbStruct.HREADYOUT, $bits(ahbStruct.HREADYOUT), UVM_BIN);
  printer.print_field("HRESP", ahbStruct.HRESP, $bits(ahbStruct.HRESP), UVM_BIN);
  printer.print_field("HEXOKAY", ahbStruct.HEXOKAY, $bits(ahbStruct.HEXOKAY), UVM_BIN);
  printer.print_field("HREADY", ahbStruct.HREADY, $bits(ahbStruct.HREADY), UVM_BIN);

endfunction : do_print


`endif : AHBSLAVESEQUENCEITEMCONVERTER_INCLUDED_
