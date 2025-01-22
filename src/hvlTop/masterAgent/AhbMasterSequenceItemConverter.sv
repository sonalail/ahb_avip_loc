 
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
// Function: fromClass
//  Converting seq_item transactions into struct data items
//
// Parameters:
//  name - AhbMasterTransaction, ahbTransferCharStruct
//--------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::fromClass(input AhbMasterTransaction inputConv, output ahbTransferCharStruct outputConv);
  `uvm_info("AhbMasterSequenceItemConverterClass",$sformatf("-------------------------------------------------------------"),UVM_HIGH);

  $cast(outputConv.hprot, inputConv.hprot);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hprot = %b", outputConv.hprot), UVM_HIGH);

  $cast(outputConv.hburst, inputConv.hburst);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hburst = %b", outputConv.hburst), UVM_HIGH);

  outputConv.hmastlock = inputConv.hmastlock;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hmastlock = %b", outputConv.hmastlock), UVM_HIGH);

  $cast(outputConv.hsize, inputConv.hsize);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hsize = %b", outputConv.hsize), UVM_HIGH);

  outputConv.hnonsec = inputConv.hnonsec;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hnonsec = %b", outputConv.hnonsec), UVM_HIGH);

  outputConv.hexcl = inputConv.hexcl;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hexcl = %b", outputConv.hexcl), UVM_HIGH);

  $cast(outputConv.hmaster, inputConv.hmaster);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hmaster = %b", outputConv.hmaster), UVM_HIGH);

  $cast(outputConv.htrans, inputConv.htrans);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing htrans = %b", outputConv.htrans), UVM_HIGH);

  outputConv.hwdata = inputConv.hwdata;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hwdata = %0h", outputConv.hwdata), UVM_HIGH);

  outputConv.hwstrb = inputConv.hwstrb;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hwstrb = %b", outputConv.hwstrb), UVM_HIGH);

  outputConv.hwrite = inputConv.hwrite;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hwrite = %b", outputConv.hwrite), UVM_HIGH);

  outputConv.hrdata = inputConv.hrdata;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hrdata = %0h", outputConv.hrdata), UVM_HIGH);

  outputConv.hreadyout = inputConv.hreadyout;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hreadyout = %b", outputConv.hreadyout), UVM_HIGH);

  $cast(outputConv.hresp, inputConv.hresp);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hresp = %b", outputConv.hresp), UVM_HIGH);

 /* outputConv.hexokay = inputConv.hexokay;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hexokay = %b", outputConv.hexokay), UVM_HIGH);
*/
  outputConv.hready = inputConv.hready;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hready = %b", outputConv.hready), UVM_HIGH);

  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : fromClass


//--------------------------------------------------------------------------------------------
// Function: toClass
// Converting struct data items into seq_item transactions
//
// Parameters:
// name - AhbMasterTransaction, ahbTransferCharStruct
//--------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::toClass(input ahbTransferCharStruct inputConv, ref AhbMasterTransaction outputConv);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

  $cast(outputConv.hprot, inputConv.hprot);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hprot = %b", outputConv.hprot), UVM_HIGH);

  $cast(outputConv.hburst, inputConv.hburst);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hburst = %b", outputConv.hburst), UVM_HIGH);

  outputConv.hmastlock = inputConv.hmastlock;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hmastlock = %b", outputConv.hmastlock), UVM_HIGH);

  $cast(outputConv.hsize, inputConv.hsize);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hsize = %b", outputConv.hsize), UVM_HIGH);

  outputConv.hnonsec = inputConv.hnonsec;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hnonsec = %b", outputConv.hnonsec), UVM_HIGH);

  outputConv.hexcl = inputConv.hexcl;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hexcl = %b", outputConv.hexcl), UVM_HIGH);

  $cast(outputConv.hmaster, inputConv.hmaster);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hmaster = %b", outputConv.hmaster), UVM_HIGH);

  $cast(outputConv.htrans, inputConv.htrans);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing htrans = %b", outputConv.htrans), UVM_HIGH);

  outputConv.hwdata = inputConv.hwdata;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hwdata = %0h", outputConv.hwdata), UVM_HIGH);

  outputConv.hwstrb = inputConv.hwstrb;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hwstrb = %b", outputConv.hwstrb), UVM_HIGH);

  outputConv.hwrite = inputConv.hwrite;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hwrite = %b", outputConv.hwrite), UVM_HIGH);

  outputConv.hrdata = inputConv.hrdata;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hrdata = %0h", outputConv.hrdata), UVM_HIGH);

  outputConv.hreadyout = inputConv.hreadyout;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hreadyout = %b", outputConv.hreadyout), UVM_HIGH);

  $cast(outputConv.hresp, inputConv.hresp);
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hresp = %b", outputConv.hresp), UVM_HIGH);

/*  outputConv.hexokay = inputConv.hexokay;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hexokay = %b", outputConv.hexokay), UVM_HIGH);
*/
  outputConv.hready = inputConv.hready;
  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("After randomizing hready = %b", outputConv.hready), UVM_HIGH);

  `uvm_info("AhbMasterSequenceItemConverterClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : toClass

//--------------------------------------------------------------------------------------------
// Function : do_print method
//  Print method can be added to display the data members values
//---------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::do_print(uvm_printer printer);
 ahbTransferCharStruct ahbStruct;
  super.do_print(printer);

  printer.print_field("hprot", ahbStruct.hprot, $bits(ahbStruct.hprot), UVM_BIN);
  printer.print_field("hburst", ahbStruct.hburst, $bits(ahbStruct.hburst), UVM_BIN);
  printer.print_field("hmastlock", ahbStruct.hmastlock, $bits(ahbStruct.hmastlock), UVM_BIN);
  printer.print_field("hsize", ahbStruct.hsize, $bits(ahbStruct.hsize), UVM_BIN);
  printer.print_field("hnonsec", ahbStruct.hnonsec, $bits(ahbStruct.hnonsec), UVM_BIN);
  printer.print_field("hexcl", ahbStruct.hexcl, $bits(ahbStruct.hexcl), UVM_BIN);
  printer.print_field("hmaster", ahbStruct.hmaster, $bits(ahbStruct.hmaster), UVM_BIN);
  printer.print_field("htrans", ahbStruct.htrans, $bits(ahbStruct.htrans), UVM_BIN);
  printer.print_field("hwdata", ahbStruct.hwdata, $bits(ahbStruct.hwdata), UVM_HEX);
  printer.print_field("hwstrb", ahbStruct.hwstrb, $bits(ahbStruct.hwstrb), UVM_BIN);
  printer.print_field("hwrite", ahbStruct.hwrite, $bits(ahbStruct.hwrite), UVM_BIN);
  printer.print_field("hrdata", ahbStruct.hrdata, $bits(ahbStruct.hrdata), UVM_HEX);
  printer.print_field("hreadyout", ahbStruct.hreadyout, $bits(ahbStruct.hreadyout), UVM_BIN);
  printer.print_field("hresp", ahbStruct.hresp, $bits(ahbStruct.hresp), UVM_BIN);
//  printer.print_field("hexokay", ahbStruct.hexokay, $bits(ahbStruct.hexokay), UVM_BIN);
  printer.print_field("hready", ahbStruct.hready, $bits(ahbStruct.hready), UVM_BIN);
endfunction : do_print  

`endif




