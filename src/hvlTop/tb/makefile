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
	echo "make simulate_<test> uvm_verbosity=<VERBOSITY_LEVEL>";
	echo "";
	echo "Example:";
	echo "make simulate_master uvm_verbosity=UVM_HIGH";
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-----------------------------------------------------------------";
	echo "";

# Default action
all:
	make clean; make compile; make simulate;

# Compilation targets for each testbench
compile:
	make clean_compile;
	make compile_cover;
	make compile_master;
	make compile_slave;

compile_cover:
	vlog -sv +acc +cover +fcover $(comp_args) -l AhbCoverPropertyCompile.log -f ./ahbAssertion.f;
	make compile_war_err log=AhbCoverPropertyCompile.log;

compile_master:
	vlog -sv +acc +cover +fcover $(comp_args) -l AhbMasterAssertionsCompile.log -f ./ahbAssertion.f;
	make compile_war_err log=AhbMasterAssertionsCompile.log;

compile_slave:
	vlog -sv +acc +cover +fcover $(comp_args) -l AhbSlaveAssertionsCompile.log -f ./ahbAssertion.f;
	make compile_war_err log=AhbSlaveAssertionsCompile.log;

# Default verbosity level
ifndef uvm_verbosity
override uvm_verbosity = UVM_MEDIUM
endif

# Simulation targets for each testbench
simulate:
	make simulate_cover;
	make simulate_master;
	make simulate_slave;

simulate_cover:
	make run_simulation test=AhbCoverPropertyTb;

simulate_master:
	make run_simulation test=AhbMasterAssertionTb;

simulate_slave:
	make run_simulation test=AhbSlaveAssertionTb;

# Common simulation rule
run_simulation:
	mkdir -p $(test);
	vsim -vopt \
	work.$(test) \
	-voptargs=+acc=npr \
	-assertdebug \
	+UVM_TESTNAME=$(test) \
	+UVM_VERBOSITY=$(uvm_verbosity) \
	-l $(test)/$(test).log \
	-sva \
	-coverage \
	-c -do "log -r /*; add wave -r /*; coverage save -onexit -assert -directive -cvg -codeAll $(test)/coverage.ucdb; run -all; exit" \
	-wlf $(test)/waveform.wlf;
	make simulate_war_err test=$(test);

# Cleanup rules
clean_simulate:
	rm -rf AhbCoverPropertyTb AhbMasterAssertionTb AhbSlaveAssertionTb;
	rm -rf *_test/ *_test.log;  # Be more specific if needed

clean_compile:
	rm -rf work/ *.log transcript waveform.wlf;
	rm -rf merged_coverage.ucdb merged_cov_html_report;
	rm -rf *.ucdb *.wlf;  # Remove any leftover coverage and waveform files

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
	echo "------------------- Compilation Report ($$log) -----------------";
	echo "";
	grep "^** " $$log || true;
	echo "";
	grep "^Error" $$log || true;
	echo "";
	grep "^Info" $$log || true;
	echo "";
	echo "Log file path: $$log";
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-----------------------------------------------------------------";
	echo "";

# Simulation warning/error check for each testbench
simulate_war_err:
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-------------------- Simulation Report for $(test) -----------------";
	echo "";
	echo "Simulator Errors";
	grep "Error" $(test)/$(test).log || true;
	echo "";
	grep "Info" $(test)/$(test).log || true;
	echo "";
	echo "UVM Issues (Fatal, Errors, Warnings)";
	grep -E "UVM_(FATAL|ERROR|WARNING)" $(test)/$(test).log || true;
	echo "";
	echo "Testname: $(test)";
	echo "";
	echo "Log file path: $(test)/$(test).log";
	echo "";
	echo "Waveform: vsim -view $(test)/waveform.wlf &";
	echo "";
	echo "Coverage report: firefox $(test)/html_cov_report/index.html &";
	echo "";
	echo "-----------------------------------------------------------------";
	echo "-----------------------------------------------------------------";
	echo "";
