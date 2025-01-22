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
    extern static function void fromClass(input AhbMasterAgentConfig inputConv, output ahbTransferConfigStruct outputConv);
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
// Function: fromClass
//  Converting AhbMasterConfig configurations into structure configutrations
//--------------------------------------------------------------------------------------------
    function void AhbMasterConfigConverter::fromClass(input AhbMasterAgentConfig inputConv,output ahbTransferConfigStruct outputConv);
  outputConv.haddr = inputConv.haddr;
  `uvm_info("AhbMasterConfigConverter",$sformatf("after randomizing addr = \n %p",outputConv.haddr),UVM_HIGH);

endfunction : fromClass

//---------------------------------------------------------------------------------------------
// Function: do_print method
// print method can be added to display the data members values
//---------------------------------------------------------------------------------------------
function void AhbMasterConfigConverter::do_print(uvm_printer printer);

  ahbTransferConfigStruct ahbStruct;
  super.do_print(printer);
  printer.print_field( "haddr", ahbStruct.haddr , $bits(ahbStruct.haddr),UVM_DEC);

endfunction : do_print

`endif

