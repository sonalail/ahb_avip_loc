# Makefile for AHB Master, Slave Assertions, and Cover Property Testbench

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
	vlog -sv +acc +cover +fcover $(comp_args) -l AhbCoverPropertyCompile.log -f ./ahbCoverProperty.f;
	vlog -sv +acc +cover +fcover $(comp_args) -l AhbMasterAssertionsCompile.log -f ./ahbAssertion.f;
	vlog -sv +acc +cover +fcover $(comp_args) -l AhbSlaveAssertionsCompile.log -f ./ahbAssertion.f;
	make compile_war_err;
	make compile_war_err_sassert;
	make compile_war_err_massert;
	make compile_war_err_cproperty;

# Default test configuration
ifndef test
tests = AhbCoverPropertyTb AhbMasterAssertionTb AhbSlaveAssertionTb
endif

# Default verbosity level
ifndef uvm_verbosity
override uvm_verbosity = UVM_MEDIUM
endif

# Default test folder
ifndef test_folder
override test_folder = $(test)
endif

simulate:
	@for t in $(tests); do \
		mkdir -p $$t; \
		vsim -vopt \
		work.$$t \t
		-voptargs=+acc=npr \
		-assertdebug \
		+UVM_TESTNAME=$$t \
		+UVM_VERBOSITY=$(uvm_verbosity) \
		-l $$t/$$t.log \
		-sva \
		-coverage \
		-c -do "log -r /*; add wave -r /*; coverage save -onexit -assert -directive -cvg -codeAll $$t/coverage.ucdb; run -all; exit" \
		-wlf $$t/waveform.wlf; \
		make simulate_war_err test=$$t; \
		make simulate_war_err_sassert test=$$t; \
		make simulate_war_err_massert test=$$t; \
		make simulate_war_err_cproperty test=$$t; \
	done

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

# Compilation warning/error check (covers all tests)
compile_war_err:
	@for log in AhbCoverPropertyCompile.log AhbMasterAssertionsCompile.log AhbSlaveAssertionsCompile.log; do \
		echo ""; \
		echo "-----------------------------------------------------------------"; \
		echo "------------------- Compilation Report ($$log) -----------------"; \
		echo ""; \
		grep "^** " $$log || true; \
		echo ""; \
		grep "^Error" $$log || true; \
		echo ""; \
		grep "^Info" $$log || true; \
		echo ""; \
		echo "Log file path: $$log"; \
		echo ""; \
		echo "-----------------------------------------------------------------"; \
		echo "-----------------------------------------------------------------"; \
		echo ""; \
	done

# Simulation warning/error check (covers all tests)
simulate_war_err:
	@for t in $(tests); do \
		echo ""; \
		echo "-----------------------------------------------------------------"; \
		echo "-------------------- Simulation Report for $$t -----------------"; \
		echo ""; \
		echo "Simulator Errors"; \
		grep "Error" $$t/$$t.log || true; \
		echo ""; \
		grep "Info" $$t/$$t.log || true; \
		echo ""; \
		echo "UVM Fatal"; \
    		grep "UVM_FATAL" $$t/$$t.log || true; \
    		echo ""; \
    		echo "UVM Errors"; \
    		grep "UVM_ERROR" $$t/$$t.log || true; \
    		echo ""; \
    		echo "UVM Warnings"; \
    		grep "UVM_WARNING" $$t/$$t.log || true; \
    		echo ""; \
    		echo "Testname: $$t"; \
    		echo ""; \
    		echo "Log file path: $$t/$$t.log"; \
    		echo ""; \
    		echo "Waveform: vsim -view $$t/waveform.wlf &"; \
    		echo ""; \
    		echo "Coverage report: firefox $$t/html_cov_report/index.html &"; \
    		echo ""; \
    		echo "-----------------------------------------------------------------"; \
    		echo "-----------------------------------------------------------------"; \
    		echo ""; \
	done
