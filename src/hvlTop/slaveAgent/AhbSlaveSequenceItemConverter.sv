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
      `uvm_info("ahbSlaveSequeceItemconverterClass",$sformat("-------------------------------------------------------------"),UVM_HIGH);

      $cast(outputConv.hprot, inputConv.hprot);
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hprot = %b", output_conv.hprot), UVM_HIGH);

      $cast(outputConv.hburst, inputConv.hburst);
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hburst = %b", output_conv.hburst), UVM_HIGH);

      outputConv.hmastlock = inputConv.hmastlock;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hmastlock = %b", output_conv.hmastlock), UVM_HIGH);

      $cast(outputConv.hsize, inputConv.hsize);
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hsize = %b", output_conv.hsize), UVM_HIGH);

      outputConv.hnonsec = inputConv.hnonsec;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hnonsec = %b", output_conv.hnonsec), UVM_HIGH);

      outputConv.hexcl = inputConv.hexcl;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hexcl = %b", output_conv.hexcl), UVM_HIGH);

      $cast(outputConv.hmaster, inputConv.hmaster);
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hmaster = %b", output_conv.hmaster), UVM_HIGH);

      $cast(outputConv.htrans, inputConv.htrans);
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing htrans = %b", output_conv.htrans), UVM_HIGH);

      outputConv.hwdata = inputConv.hwdata;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hwdata = %0h", output_conv.hwdata), UVM_HIGH);

      outputConv.hwstrb = inputConv.hwstrb;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hwstrb = %b", output_conv.hwstrb), UVM_HIGH);

      outputConv.hwrite = inputConv.hwrite;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hwrite = %b", output_conv.hwrite), UVM_HIGH);

      outputConv.hrdata = inputConv.hrdata;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hrdata = %0h", output_conv.hrdata), UVM_HIGH);

      outputConv.hreadyout = inputConv.hreadyout;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hreadyout = %b", output_conv.hreadyout), UVM_HIGH);

      $cast(outputConv.hresp, inputConv.hresp);
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hresp = %b", output_conv.hresp), UVM_HIGH);

      /*
      output_conv.hexokay = input_conv.hexokay;
      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("After randomizing hexokay = %b", output_conv.hexokay), UVM_HIGH);
      */

      `uvm_info("ahbSlaveSequeceItemconverterClass", $sformat("-------------------------------------------------------------"), UVM_HIGH);


endfunction : fromClass 

//--------------------------------------------------------------------------------------------
// Function: toClass
// Converting struct data items into seq_item transactions
//
// Parameters:
// name - AhbSlaveTransaction, ahbTransferCharStruct
//--------------------------------------------------------------------------------------------
    function void AhbSlaveSequenceItemConverter::toClass(input ahbTransferCharStruct inputConv, ref AhbSlaveTransaction outputConv);
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

  $cast(outputConv.hprot, inputConv.hprot);
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hprot = %b", output_conv.hprot), UVM_HIGH);

  $cast(outputConv.hburst, inputConv.hburst);
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hburst = %b", output_conv.hburst), UVM_HIGH);

  outputConv.hmastlock = inputConv.hmastlock;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hmastlock = %b", output_conv.hmastlock), UVM_HIGH);

  $cast(outputConv.hsize, inputConv.hsize);
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hsize = %b", output_conv.hsize), UVM_HIGH);

  outputConv.hnonsec = inputConv.hnonsec;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hnonsec = %b", output_conv.hnonsec), UVM_HIGH);

  outputConv.hexcl = inputConv.hexcl;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hexcl = %b", output_conv.hexcl), UVM_HIGH);

  $cast(outputConv.hmaster, inputConv.hmaster);
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hmaster = %b", output_conv.hmaster), UVM_HIGH);

  $cast(outputConv.htrans, inputConv.htrans);
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing htrans = %b", output_conv.htrans), UVM_HIGH);

  outputConv.hwdata = inputConv.hwdata;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hwdata = %0h", output_conv.hwdata), UVM_HIGH);

  outputConv.hwstrb = inputConv.hwstrb;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hwstrb = %b", output_conv.hwstrb), UVM_HIGH);

  outputConv.hwrite = inputConv.hwrite;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hwrite = %b", output_conv.hwrite), UVM_HIGH);

  outputConv.hrdata = inputConv.hrdata;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hrdata = %0h", output_conv.hrdata), UVM_HIGH);

 outputConv.hreadyout = inputConv.hreadyout;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hreadyout = %b", output_conv.hreadyout), UVM_HIGH);

  $cast(outputConv.hresp, inputConv.hresp);
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hresp = %b", output_conv.hresp), UVM_HIGH);

  /*
  output_conv.hexokay = input_conv.hexokay;
  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("After randomizing hexokay = %b", output_conv.hexokay), UVM_HIGH);
  */

  `uvm_info("AhbSlaveSequenceItemConverterClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : toClass

//-------------------------------------------------------
// Function: do_print
//  This function is used to print the sequence item data from the AhbSlaveSequenceItemConverter class
//-------------------------------------------------------
function void AhbSlaveSequenceItemConverter::do_print(uvm_printer printer);
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
// printer.print_field("hexokay", ahbStruct.hexokay, $bits(ahbStruct.hexokay), UVM_BIN);
printer.print_field("hready", ahbStruct.hready, $bits(ahbStruct.hready), UVM_BIN);

endfunction : do_print


`endif 
