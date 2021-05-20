# AutoSVA

AutoSVA was build with the goal of making Formal Property Verification (FPV) more accesible for hardware designers. AutoSVA brings a simple language to make annotations in the signal declaration section of a module interface. This enables our to generate Formal Testbenches (FT) that check that transactions between hardware RTL modules follow their interface especifications. It does not check full correctness of the design but it automatically generate liveness properties (prevent duplicated responses, prevent requests being dropped) and some safety-relate properties of transactions, like data integrity, transaction invariants, uniqueness, stability... To understand this more fully you can read the pre-print version of our paper at https://arxiv.org/abs/2104.04003. AutoSVA will be publised at the 58th Design and Automation Conference (DAC'21).

## Script parameters

The AutoSVA tool is based on a Python script, which takes the next arguments

    Required argument
      -f FILENAME, --filename FILENAME
                            Path to DUT RTL module file.
    Optional arguments
      -h, --help            show this help message and exit
      -src SOURCE [SOURCE ...], --source SOURCE [SOURCE ...]
                        Path to source code folder where submodules are.
      -i INCLUDE, --include INCLUDE
                        Path to include folder that DUT and submodules use.
      -as SUBMODULE_ASSERT [SUBMODULE_ASSERT ...], --submodule_assert SUBMODULE_ASSERT [SUBMODULE_ASSERT ...]
                        List of submodules for which ASSERT the behavior of
                        outgoing transactions.
      -am SUBMODULE_ASSUME [SUBMODULE_ASSUME ...], --submodule_assume SUBMODULE_ASSUME [SUBMODULE_ASSUME ...]
                        List of submodules for which ASSUME the behavior of
                        outgoing transactions (ASSUME can constrain the DUT).
      -x [XPROP_MACRO], --xprop_macro [XPROP_MACRO]
                        Generate X Propagation assertions, specify argument to
                        create property under <MACRO> (default none)
      -tool [TOOL]      Backend tool to use [jasper|sby] (default sby)

For example:

    python autosva.py -f <DUT_PATH/DUT_NAME.v> -v 1 -src <SRC_PATH> -i <INCLUDE_PATH>

You can set the flag -v to generate the verbose output and see the parsing process

Once the FT is generated, you can run the FT on SBY like this:

   ./run.sh <DUT_NAME>

## Troubleshooting

SVA files at the Formal Testbench (FT) are auto-generated every time you execute autosva_py on a DUT_NAME, but manual commands can be added manually to ft_<DUT_NAME>/FPV.sby, for example, to solve the next cases:

A) When SBY is elaborating the project, if it complains about any RTL submodule or include not being found, add its path manually (more info at https://symbiyosys.readthedocs.io/en/latest/)

B) Alternatively, you can add blackbox <submodule> for those submodule if you want to blackbox them

C) If the RTL needs some defines to be set, do so also by appending "read -define <NAME>=1" after "read -verific"

## Reproduce Results at Ariane

### Requirements

SBY with Verific frontend, e.g. provided by yosyshq.com (to run with -tool sby backend)
JasperGold version 2015.12 or superior (to run with -tool jasper backend)
Python version 2 or superior

### Commands

    # Clone the Ariane repository with the annotations to the modules
    git clone https://github.com/morenes/cva6.git ariane
    cd ariane
    git checkout autosva
    git submodule update --init --recursive --force src
    cd ..

    # Set DUT_ROOT and AUTOSVA_ROOT env variable
    export DUT_ROOT=$PWD/ariane
    export AUTOSVA_ROOT=$PWD

    # Enter AutoSVA folder and run scripts to update relative Formal Testbenches (FT)
    cd autosva 
    ./setup_ariane.sh
    ./run.sh mmu      # lsu_lookup_transid_was_a_request shows the ghost response bug
    

## Quickstart tutorial. Reproduce the steps.
The tutorial is 14 minutes and it is available at https://www.youtube.com/watch?v=Gb5wT1D7dxU.
In the tutorial we create a Formal Property Verification (FPV) testbench for a FIFO queue. We show step by step how to generate it by adding 3 lines of code of annotations and simply pressing the play button. Our transaction abstraction is applicable to many more modules, and out explicit annotations provide flexibility of names and interface styles, e.g. we support annotating when interfaces use structs, or when transactions do not seem obvious at first.
    
### Commands used
    export DUT_ROOT=$PWD/quickstart 
    export AUTOSVA_ROOT=$PWD
    
 Then we added the following annotations to the fifo.v inside the quickstart folder
    
     /*AUTOSVA 
     fifo: in -IN> out
     [INFLIGHT_IDX-1:0] in_transid = fifo.buffer_head_r
     [INFLIGHT_IDX-1:0] out_transid = fifo.buffer_tail_r
     */
 
 Then we run the autosva tool, what will generate the formal testbench called 'ft_fifo':
    
     python autosva.py -f fifo.v -x XPROP -tool sby
    
 Then we run the formal property verification tool, in this case SBY. We use the run script to run the fifo FT
    
     ./run.sh fifo
    
 To watch the waveforms of a Counterexample (CEX) we used 
    
     gtkwave ft_fifo/FPV_prv/engine_0/trace.vcd &
