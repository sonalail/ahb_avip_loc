`ifndef AHBMASTERCONFIGCONVERTER_INCLUDED_
`define AHBMASTERCONFIGCONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterConfigConverter
// Description:
// class for converting masterConfig configuration into struct configurations
//--------------------------------------------------------------------------------------------
class AhbMasterConfigConverter extends uvm_object;
  `uvm_object_utils(AhbMasterConfigConverter)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterConfigConverter");
    extern static function void from_class(input AhbMasterAgentConfig inputConv, output ahbTransferConfigStruct outputConv);
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
    function void AhbMasterConfigConverter::fromClass(input AhbMasterAgentConfig ahbMasterAgentConfig,output ahbTransferConfigStruct outputConv);
  outputConv.HADDR = ahbMasterAgentConfig.HADDR;
  `uvm_info("AhbMasterConfigConverter",$sformatf("after randomizing addr = \n %p",outputConv.HADDR),UVM_HIGH);

endfunction : from_class

//---------------------------------------------------------------------------------------------
// Function: do_print method
// print method can be added to display the data members values
//---------------------------------------------------------------------------------------------
function void AhbMasterConfigConverter::do_print(uvm_printer printer);

  ahbTransferConfigStruct ahbSt;
  super.do_print(printer);
  printer.print_field( "haddr", ahbSt.HADDR , $bits(ahbSt.HADDR),UVM_DEC);

endfunction : do_print

`endif

