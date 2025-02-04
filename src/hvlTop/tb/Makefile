# Makefile for AHB Master Assertions Testbench

# Default target
usage:
	echo "";
	echo "-----------------------------------------------------------------";
	echo "------------------------- Usage ---------------------------------";
	echo "";
	echo "make target <options> <variable>=<value>";
	echo "";
	echo "To compile use:";
	echo "make compile";
	echo "";
	echo "To provide compilation arguments:";
	echo "make compile comp_args=\"+define+<macro_name>=<value>\"";
	echo "";
	echo "Example:";
	echo "make compile comp_args=\"+define+ADDR_WIDTH=64 +define+DATA_WIDTH=64\"";
	echo "";
	echo "To simulate a test:";
	echo "make simulate test=<test_name> uvm_verbosity=<VERBOSITY_LEVEL>";
	echo "";
	echo "Example:";
	echo "make simulate test=ahb_master_test uvm_verbosity=UVM_HIGH";
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-----------------------------------------------------------------";
	echo "";

# Default action
all:
	make clean; make compile; make simulate;

# Compilation target
compile:
	make clean_compile;
	make clean_simulate;
	vlib work;
	vlog -sv \
	+acc \
	+cover \
	+fcover \
	$(comp_args) \
	-l AhbCoverPropertyCompile.log \
	-f ./ahbCoverProperty.f;
	Make compile_war_err;

# Default test configuration
ifndef test
override test = AhbCoverPropertyTb
endif

# Default verbosity level
ifndef uvm_verbosity
override uvm_verbosity = UVM_MEDIUM
endif

# Default test folder
ifndef test_folder
override test_folder = $(test)
endif

# Simulation target
simulate:
	mkdir -p $(test_folder);
	vsim -vopt \
	work.$(test) \
	-voptargs=+acc=npr \
	-assertdebug \
	+UVM_TESTNAME=$(test) \
	+UVM_VERBOSITY=$(uvm_verbosity) \
	-l $(test_folder)/$(test).log \
	-sva \
	-coverage \
	-c -do "log -r /*; add wave -r /*; coverage save -onexit -assert -directive -cvg -codeAll $(test_folder)/$(test_folder)_coverage.ucdb; run -all; exit" \
	-wlf $(test_folder)/waveform.wlf;
	make simulate_war_err;

# Cleanup rules
clean_simulate:
	rm -rf *_test*;

clean_compile:
	rm -rf work/ *_compile.log transcript waveform.wlf;
	rm -rf merged_coverage.ucdb merged_cov_html_report;

# Coverage merge and reporting
merge_cov_report:
	rm -rf merged_coverage.ucdb merged_cov_html_report;
	vcover merge merged_coverage.ucdb -64 */*.ucdb;
	vcover report -html merged_coverage.ucdb -htmldir ./merged_cov_html_report -details;
	echo "";
	echo "-----------------------------------------------------------------";
	echo "Coverage report: firefox merged_cov_html_report/index.html &";
	echo "-----------------------------------------------------------------";
	echo "";

# Compilation warning/error check
compile_war_err:
	echo "";
	echo "-----------------------------------------------------------------";
	echo "------------------- Compilation Report --------------------------";
	echo "";
	grep "^** " AhbCoverPropertyCompile.log;
	echo "";
	grep "^Error" AhbCoverPropertyCompile.log;
	echo "";
	grep "^Info" AhbCoverPropertyCompile.log;
	echo "";
	echo "Log file path: AhbCoverPropertyCompile.log";
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-----------------------------------------------------------------";
	echo "";

# Simulation warning/error check
simulate_war_err:
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-------------------- Simulation Report --------------------------";
	echo "";
	echo "Simulator Errors";
	grep "Error" $(test_folder)/$(test).log;
	echo "";
	grep "Info" $(test_folder)/$(test).log;
	echo "";
	echo "UVM Fatal";
	grep "UVM_FATAL" $(test_folder)/$(test).log;
	echo "";
	echo "UVM Errors";
	grep "UVM_ERROR" $(test_folder)/$(test).log;
	echo "";
	echo "UVM Warnings";
	grep "UVM_WARNING" $(test_folder)/$(test).log;
	echo "";
	echo "Testname: $(test)";
	echo "";
	echo "Log file path: $(test_folder)/$(test).log";
	echo "";
	echo "Waveform: vsim -view $(test_folder)/waveform.wlf &";
	echo "";
	echo "Coverage report: firefox $(test_folder)/html_cov_report/index.html &";
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-----------------------------------------------------------------";
	echo "";
