`ifndef AHB_MASTER_CFG_CONVERTER_INCLUDED_
`define AHB_MASTER_CFG_CONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterConfigConverter
// Description:
// class for converting master_cfg configuration into struct configurations
//--------------------------------------------------------------------------------------------
class AhbMasterConfigConverter extends uvm_object;
  `uvm_object_utils(AhbMasterConfigConverter)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterConfigConverter");
  extern static function void from_class(input AhbMasterAgentConfig input_conv_h, output ahb_transfer_cfg_s output_conv);
  extern function void do_print(uvm_printer printer);

endclass : AhbMasterConfigConverter

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
// name - AhbMasterConfigConverter
//--------------------------------------------------------------------------------------------
function AhbMasterConfigConverter::new(string name = "AhbMasterConfigConverter");
  super.new(name);
endfunction : new

//-------------------------------------------------------------------------------------------
// Function: from_class
//  Converting AhbMasterConfig configurations into structure configutrations
//--------------------------------------------------------------------------------------------
function void AhbMasterConfigConverter::from_class(input AhbMasterAgentConfig input_conv_h, 
                                                   output ahb_transfer_cfg_s output_conv);
  output_conv.HADDR = input_conv_h.HADDR; 
  `uvm_info("AhbMasterConfigConverter",$sformatf("after randomizing addr = \n %p",output_conv.HADDR),UVM_HIGH);

endfunction : from_class

//---------------------------------------------------------------------------------------------
// Function: do_print method
// print method can be added to display the data members values
//---------------------------------------------------------------------------------------------
function void AhbMasterConfigConverter::do_print(uvm_printer printer);
  
  ahb_transfer_cfg_s ahb_st;
  super.do_print(printer);
  printer.print_field( "paddr", ahb_st.HADDR , $bits(ahb_st.HADDR),UVM_DEC);

endfunction : do_print

`endif

