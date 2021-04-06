# AutoSVA

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

C) If the RTL needs some defines to be set, do so also by appending "read -define <NAME>=1" after read -verific

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

    # Set ARIANE_REPO env variable
    export ARIANE_REPO=$PWD/ariane

    # Enter AutoSVA folder and run scripts to update relative Formal Testbenches (FT)
    cd autosva 
    ./setup_ariane.sh
    ./run.sh mmu      # lsu_lookup_transid_was_a_request shows the ghost response bug
    

