`ifndef AHB_SLAVE_SEQ_ITEM_CONVERTER_INCLUDED_
`define AHB_SLAVE_SEQ_ITEM_CONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class : AhbSlaveSequenceItemConverter
//  This class converts seq_item transactions into struct data items and vice versa
//--------------------------------------------------------------------------------------------
class AhbSlaveSequenceItemConverter extends uvm_object;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveSequenceItemConverter");
  extern static function void from_class(input ahb_slave_tx input_conv, output ahb_transfer_char_s output_conv);
  extern static function void to_class(input ahb_transfer_char_s input_conv, ref ahb_slave_tx output_conv_h);
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
// Function: from_class
//  Converting seq_item transactions into struct data items
//
// Parameters:
//  name - ahb_slave_tx, ahb_transfer_char_s
//--------------------------------------------------------------------------------------------
function void AhbSlaveSequenceItemConverter::from_class(input ahb_slave_tx input_conv, output ahb_transfer_char_s output_conv);
  `uvm_info("AhbSlaveSeqItemConvClass",$sformatf("-------------------------------------------------------------"),UVM_HIGH);

  $cast(output_conv.HPROT, input_conv.HPROT);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HPROT = %b", output_conv.HPROT), UVM_HIGH);

  $cast(output_conv.HBURST, input_conv.HBURST);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HBURST = %b", output_conv.HBURST), UVM_HIGH);

  output_conv.HMASTLOCK = input_conv.HMASTLOCK;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", output_conv.HMASTLOCK), UVM_HIGH);

  $cast(output_conv.HSIZE, input_conv.HSIZE);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", output_conv.HSIZE), UVM_HIGH);

  output_conv.HNONSEC = input_conv.HNONSEC;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", output_conv.HNONSEC), UVM_HIGH);

  output_conv.HEXCL = input_conv.HEXCL;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", output_conv.HEXCL), UVM_HIGH);

  $cast(output_conv.HMASTER, input_conv.HMASTER);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", output_conv.HMASTER), UVM_HIGH);

  $cast(output_conv.HTRANS, input_conv.HTRANS);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", output_conv.HTRANS), UVM_HIGH);

  output_conv.HWDATA = input_conv.HWDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", output_conv.HWDATA), UVM_HIGH);

  output_conv.HWSTRB = input_conv.HWSTRB;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", output_conv.HWSTRB), UVM_HIGH);

  output_conv.HWRITE = input_conv.HWRITE;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", output_conv.HWRITE), UVM_HIGH);

  output_conv.HRDATA = input_conv.HRDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", output_conv.HRDATA), UVM_HIGH);

  output_conv.HREADYOUT = input_conv.HREADYOUT;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", output_conv.HREADYOUT), UVM_HIGH);

  $cast(output_conv.HRESP, input_conv.HRESP);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRESP = %b", output_conv.HRESP), UVM_HIGH);

  output_conv.HEXOKAY = input_conv.HEXOKAY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", output_conv.HEXOKAY), UVM_HIGH);

  output_conv.HREADY = input_conv.HREADY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADY = %b", output_conv.HREADY), UVM_HIGH);

  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : from_class 

//--------------------------------------------------------------------------------------------
// Function: to_class
// Converting struct data items into seq_item transactions
//
// Parameters:
// name - ahb_slave_tx, ahb_transfer_char_s
//--------------------------------------------------------------------------------------------
function void AhbSlaveSequenceItemConverter::to_class(input ahb_transfer_char_s input_conv, ref ahb_slave_tx output_conv_h);
  `uvm_info("AhbSlaveSeqItemConv", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

  $cast(output_conv_h.HPROT, input_conv.HPROT);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HPROT = %b", output_conv_h.HPROT), UVM_HIGH);

  $cast(output_conv_h.HBURST, input_conv.HBURST);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HBURST = %b", output_conv_h.HBURST), UVM_HIGH);

  output_conv_h.HMASTLOCK = input_conv.HMASTLOCK;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTLOCK = %b", output_conv_h.HMASTLOCK), UVM_HIGH);

  $cast(output_conv_h.HSIZE, input_conv.HSIZE);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HSIZE = %b", output_conv_h.HSIZE), UVM_HIGH);

  output_conv_h.HNONSEC = input_conv.HNONSEC;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HNONSEC = %b", output_conv_h.HNONSEC), UVM_HIGH);

  output_conv_h.HEXCL = input_conv.HEXCL;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXCL = %b", output_conv_h.HEXCL), UVM_HIGH);

  $cast(output_conv_h.HMASTER, input_conv.HMASTER);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HMASTER = %b", output_conv_h.HMASTER), UVM_HIGH);

  $cast(output_conv_h.HTRANS, input_conv.HTRANS);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HTRANS = %b", output_conv_h.HTRANS), UVM_HIGH);

  output_conv_h.HWDATA = input_conv.HWDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWDATA = %0h", output_conv_h.HWDATA), UVM_HIGH);

  output_conv_h.HWSTRB = input_conv.HWSTRB;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWSTRB = %b", output_conv_h.HWSTRB), UVM_HIGH);

  output_conv_h.HWRITE = input_conv.HWRITE;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HWRITE = %b", output_conv_h.HWRITE), UVM_HIGH);

  output_conv_h.HRDATA = input_conv.HRDATA;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRDATA = %0h", output_conv_h.HRDATA), UVM_HIGH);

  output_conv_h.HREADYOUT = input_conv.HREADYOUT;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADYOUT = %b", output_conv_h.HREADYOUT), UVM_HIGH);

  $cast(output_conv_h.HRESP, input_conv.HRESP);
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HRESP = %b", output_conv_h.HRESP), UVM_HIGH);

  output_conv_h.HEXOKAY = input_conv.HEXOKAY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HEXOKAY = %b", output_conv_h.HEXOKAY), UVM_HIGH);

  output_conv_h.HREADY = input_conv.HREADY;
  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("After randomizing HREADY = %b", output_conv_h.HREADY), UVM_HIGH);

  `uvm_info("AhbSlaveSeqItemConvClass", $sformatf("-------------------------------------------------------------"), UVM_HIGH);

endfunction : to_class

//-------------------------------------------------------
// Function: do_print
//  This function is used to print the sequence item data from the AhbSlaveSequenceItemConverter class
//-------------------------------------------------------
function void AhbSlaveSequenceItemConverter::do_print(uvm_printer printer);
  ahb_transfer_char_s ahb_st;
  super.do_print(printer);

  printer.print_field("HPROT", ahb_st.HPROT, $bits(ahb_st.HPROT), UVM_BIN);
  printer.print_field("HBURST", ahb_st.HBURST, $bits(ahb_st.HBURST), UVM_BIN);
  printer.print_field("HMASTLOCK", ahb_st.HMASTLOCK, $bits(ahb_st.HMASTLOCK), UVM_BIN);
  printer.print_field("HSIZE", ahb_st.HSIZE, $bits(ahb_st.HSIZE), UVM_BIN);
  printer.print_field("HNONSEC", ahb_st.HNONSEC, $bits(ahb_st.HNONSEC), UVM_BIN);
  printer.print_field("HEXCL", ahb_st.HEXCL, $bits(ahb_st.HEXCL), UVM_BIN);
  printer.print_field("HMASTER", ahb_st.HMASTER, $bits(ahb_st.HMASTER), UVM_BIN);
  printer.print_field("HTRANS", ahb_st.HTRANS, $bits(ahb_st.HTRANS), UVM_BIN);
  printer.print_field("HWDATA", ahb_st.HWDATA, $bits(ahb_st.HWDATA), UVM_HEX);
  printer.print_field("HWSTRB", ahb_st.HWSTRB, $bits(ahb_st.HWSTRB), UVM_BIN);
  printer.print_field("HWRITE", ahb_st.HWRITE, $bits(ahb_st.HWRITE), UVM_BIN);
  printer.print_field("HRDATA", ahb_st.HRDATA, $bits(ahb_st.HRDATA), UVM_HEX);
  printer.print_field("HREADYOUT", ahb_st.HREADYOUT, $bits(ahb_st.HREADYOUT), UVM_BIN);
  printer.print_field("HRESP", ahb_st.HRESP, $bits(ahb_st.HRESP), UVM_BIN);
  printer.print_field("HEXOKAY", ahb_st.HEXOKAY, $bits(ahb_st.HEXOKAY), UVM_BIN);
  printer.print_field("HREADY", ahb_st.HREADY, $bits(ahb_st.HREADY), UVM_BIN);

endfunction : do_print


`endif : AHB_SLAVE_SEQ_ITEM_CONVERTER_INCLUDED_
