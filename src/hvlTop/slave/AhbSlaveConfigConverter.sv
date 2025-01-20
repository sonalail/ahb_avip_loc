`ifndef APB_SLAVE_CFG_CONVERTER_INCLUDED_
`define APB_SLAVE_CFG_CONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveConfigConverter
//  Class for converting apb_slave_cfg configurations into struct configurations
//--------------------------------------------------------------------------------------------
class AhbSlaveConfigConverter extends uvm_object;
  `uvm_object_utils(AhbSlaveConfigConverter)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveConfigConverter");
    extern static function void from_class(input AhbSlaveAgentConfig input_conv_h, output ahb_transfer_cfg_s output_conv_h);
  extern function void do_print(uvm_printer printer);

endclass : AhbSlaveConfigConverter

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - AhbSlaveConfigConverter
//--------------------------------------------------------------------------------------------
function AhbSlaveConfigConverter::new(string name = "AhbSlaveConfigConverter");
  super.new(name);
endfunction : new

//-------------------------------------------------------------------------------------------
// Function: from_class
//  Converting AhbSlaveAgentConfig configurations into structure configutrations
//--------------------------------------------------------------------------------------------
function void apb_slave_cfg_converter::from_class(input AhbSlaveAgentConfig input_conv_h, 
                                                  output apb_transfer_cfg_s output_conv_h);
  
  `uvm_info("Ahb_seq_item_conv_from_class",$sformatf("--\n----------------------------------------SLAVE_CFG_CONVERTER_FROM_CLASS--------------------------------------"),UVM_HIGH);
  
  /*`uvm_info("Ahb_slave_config_converter",$sformatf("Before randomizing min_address = %0h",output_conv_h.min_address),UVM_HIGH);
  output_conv_h.min_address = input_conv_h.min_address; 
  `uvm_info("apb_slave_config_converter",$sformatf("After randomizing the min_address = %0h",output_conv_h.min_address),UVM_HIGH);

  `uvm_info("apb_slave_config_converter",$sformatf("Before randomizing max_address = %0h",output_conv_h.max_address),UVM_HIGH);
  output_conv_h.max_address = input_conv_h.max_address; 
  `uvm_info("apb_slave_config_converter",$sformatf("After randomizing the max_address = %0h",output_conv_h.max_address),UVM_HIGH);
  output_conv_h.slave_id = input_conv_h.slave_id;
  `uvm_info("AhbSlaveConfigConverter",$sformatf("After randomizing the slave_id = %0h",output_conv_h.slave_id),UVM_HIGH);
  */
  
  `uvm_info("apb_slave_config_converter","--\n------------------------------------------------------------EOP---------------------------------------------------- ",UVM_HIGH);

endfunction : from_class

//---------------------------------------------------------------------------------------------
// Function: do_print method
//  Print method can be added to display the data members values
// 
// Parameters:
//  printer   - uvm_printer
//---------------------------------------------------------------------------------------------
function void AhbSlaveConfigConverter::do_print(uvm_printer printer);
  
  ahb_transfer_cfg_s apb_st;
  super.do_print(printer);
 
  /* printer.print_field( "min_address", apb_st.min_address, $bits(apb_st.min_address),UVM_HEX);
  printer.print_field( "max_address", apb_st.max_address, $bits(apb_st.max_address),UVM_HEX);
  */
  
endfunction : do_print

`endif

