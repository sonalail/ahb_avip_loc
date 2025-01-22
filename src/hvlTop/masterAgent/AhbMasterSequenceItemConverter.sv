 
`ifndef AHBMASTERSEQUENCEITEMCONVERTER_INCLUDED_
`define AHBMASTERSEQUENCEITEMCONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class : AhbMasterSequenceItemConverter
//  This class converts seq_item transactions into struct data items and vice versa
//--------------------------------------------------------------------------------------------
class AhbMasterSequenceItemConverter extends uvm_object;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterSequenceItemConverter");
  extern static function void fromClass(input AhbMasterTransaction inputConv, output ahbTransferCharStruct  outputConv);
  extern static function void toClass(input ahbTransferCharStruct  inputConv, ref AhbMasterTransaction outputConv);
  extern function void do_print(uvm_printer printer);

endclass : AhbMasterSequenceItemConverter

//-------------------------------------------------------
// Construct:new
// 
// Parameters:
//  name - AhbMasterSequenceItemConverter
//-------------------------------------------------------
function AhbMasterSequenceItemConverter::new(string name = "AhbMasterSequenceItemConverter");
  super.new(name);
endfunction: new

//--------------------------------------------------------------------------------------------
// Function: from_class
//  Converting seq_item transactions into struct data items
//
// Parameters:
//  name - ahb_master_tx, ahbTransferCharStruct
//--------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::from_class(input AhbMasterTransaction inputConv, output ahbTransferCharStruct outputConv);
  `uvm_info("AhbMasterSeqItemConvClass",$sformatf("-------------------------------------------------------------"),UVM_HIGH);

  $cast(outputConv.HPROT, inputConv.HPROT);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HPROT = %b", outputConv.HPROT), UVM_HIGH);

  $cast(outputConv.HBURST, inputConv.HBURST);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HBURST = %b", outputConv.HBURST), UVM_HIGH);

  outputConv.HMASTLOCK = inputConv.HMASTLOCK;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", outputConv.HMASTLOCK), UVM_HIGH);

  $cast(outputConv.HSIZE, inputConv.HSIZE);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", outputConv.HSIZE), UVM_HIGH);

  outputConv.HNONSEC = inputConv.HNONSEC;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", outputConv.HNONSEC), UVM_HIGH);

  outputConv.HEXCL = inputConv.HEXCL;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", outputConv.HEXCL), UVM_HIGH);

  $cast(outputConv.HMASTER, inputConv.HMASTER);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", outputConv.HMASTER), UVM_HIGH);

  $cast(outputConv.HTRANS, inputConv.HTRANS);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", outputConv.HTRANS), UVM_HIGH);

  outputConv.HWDATA = inputConv.HWDATA;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", outputConv.HWDATA), UVM_HIGH);

  outputConv.HWSTRB = inputConv.HWSTRB;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", outputConv.HWSTRB), UVM_HIGH);

  outputConv.HWRITE = inputConv.HWRITE;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", outputConv.HWRITE), UVM_HIGH);

  outputConv.HRDATA = inputConv.HRDATA;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", outputConv.HRDATA), UVM_HIGH);

  outputConv.HREADYOUT = inputConv.HREADYOUT;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", outputConv.HREADYOUT), UVM_HIGH);

  $cast(outputConv.HRESP, inputConv.HRESP);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HRESP = %b", outputConv.HRESP), UVM_HIGH);

  outputConv.HEXOKAY = inputConv.HEXOKAY;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", outputConv.HEXOKAY), UVM_HIGH);

  outputConv.HREADY = inputConv.HREADY;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HREADY = %b", outputConv.HREADY), UVM_HIGH);

  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : from_class 

//--------------------------------------------------------------------------------------------
// Function: to_class
// Converting struct data items into seq_item transactions
//
// Parameters:
// name - ahb_master_tx, ahbTransferCharStruct
//--------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::to_class(input ahbTransferCharStruct inputConv, ref AhbMasterTransaction outputConv);
  `uvm_info("AhbMasterSeqItemConv", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

  $cast(outputConv.HPROT, inputConv.HPROT);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HPROT = %b", outputConv.HPROT), UVM_HIGH);

  $cast(outputConv.HBURST, inputConv.HBURST);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HBURST = %b", outputConv.HBURST), UVM_HIGH);

  outputConv.HMASTLOCK = inputConv.HMASTLOCK;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", outputConv.HMASTLOCK), UVM_HIGH);

  $cast(outputConv.HSIZE, inputConv.HSIZE);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", outputConv.HSIZE), UVM_HIGH);

  outputConv.HNONSEC = inputConv.HNONSEC;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", outputConv.HNONSEC), UVM_HIGH);

  outputConv.HEXCL = inputConv.HEXCL;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", outputConv.HEXCL), UVM_HIGH);

  $cast(outputConv.HMASTER, inputConv.HMASTER);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", outputConv.HMASTER), UVM_HIGH);

  $cast(outputConv.HTRANS, inputConv.HTRANS);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", outputConv.HTRANS), UVM_HIGH);

  outputConv.HWDATA = inputConv.HWDATA;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", outputConv.HWDATA), UVM_HIGH);

  outputConv.HWSTRB = inputConv.HWSTRB;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", outputConv.HWSTRB), UVM_HIGH);

  outputConv.HWRITE = inputConv.HWRITE;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", outputConv.HWRITE), UVM_HIGH);

  outputConv.HRDATA = inputConv.HRDATA;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", outputConv.HRDATA), UVM_HIGH);

  outputConv.HREADYOUT = inputConv.HREADYOUT;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", outputConv.HREADYOUT), UVM_HIGH);

  $cast(outputConv.HRESP, inputConv.HRESP);
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HRESP = %b", outputConv.HRESP), UVM_HIGH);

  outputConv.HEXOKAY = inputConv.HEXOKAY;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", outputConv.HEXOKAY), UVM_HIGH);

  outputConv.HREADY = inputConv.HREADY;
  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("After randomizing HREADY = %b", outputConv.HREADY), UVM_HIGH);

  `uvm_info("AhbMasterSeqItemConvClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : to_class

//--------------------------------------------------------------------------------------------
// Function : do_print method
//  Print method can be added to display the data members values
//---------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::do_print(uvm_printer printer);
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

`endif




