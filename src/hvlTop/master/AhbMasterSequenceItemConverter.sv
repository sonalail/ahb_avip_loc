 
`ifndef AHB_MASTER_SEQ_ITEM_CONVERTER_INCLUDED_
`define AHB_MASTER_SEQ_ITEM_CONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class : AhbMasterSequenceItemConverter
//  This class converts seq_item transactions into struct data items and vice versa
//--------------------------------------------------------------------------------------------
class AhbMasterSequenceItemConverter extends uvm_object;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterSequenceItemConverter");
  extern static function void from_class(input ahb_master_tx input_conv, output ahb_transfer_char_s output_conv);
  extern static function void to_class(input ahb_transfer_char_s input_conv, ref ahb_master_tx output_conv_h);
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
//  name - ahb_master_tx, ahb_transfer_char_s
//--------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::from_class(input ahb_master_tx input_conv, output ahb_transfer_char_s output_conv);
  // Logic to be implemented
endfunction : from_class 

//--------------------------------------------------------------------------------------------
// Function: to_class
// Converting struct data items into seq_item transactions
//
// Parameters:
// name - ahb_master_tx, ahb_transfer_char_s
//--------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::to_class(input ahb_transfer_char_s input_conv, ref ahb_master_tx output_conv_h);
  // Logic to be implemented
endfunction : to_class

//--------------------------------------------------------------------------------------------
// Function : do_print method
//  Print method can be added to display the data members values
//---------------------------------------------------------------------------------------------
function void AhbMasterSequenceItemConverter::do_print(uvm_printer printer);
  super.do_print(printer);
  // Logic to be implemented for displaying data members
endfunction : do_print  

`endif




