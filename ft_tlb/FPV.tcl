# THIS FILE IS A PLACEHOLDER, WHERE YOU WOULD NEED TO INCLUDE THE RIGHT COMMANDS
# OF JASPERGOLD ONCE YOU ADQUIRE A LICENSE AND HAVE ACCESS TO THE TOOL DOCUMENTATION

# Set paths to DUT root and FT root (edit if needed)
set DUT_ROOT <YOUR PATH TO ARIANE>
set AUTOSVA_ROOT <YOUR PATH TO AutoSVA>/AutoSVA/ft_tlb/..

# Analyze design under verification files (no edit)
set DUT_PATH ${DUT_ROOT}/src/
set SRC_PATH0 ${DUT_ROOT}/src/riscv-dbg/src/
set INC_PATH ${DUT_ROOT}/include
set PROP_PATH ${AUTOSVA_ROOT}/ft_tlb/sva

# Include property and RTL files
<USE COMMAND TO INCLUDE FILES AT> ${AUTOSVA_ROOT}/ft_tlb/files.vc

# Build design and properties
<BUILD USING THIS MODULE AS TOP> tlb

# Set up Clocks and Resets
<SET CLOCK SIGNAL> clk_i
<SET RESET SIGNAL> !rst_ni)

# Tool options, run and report proof results
<SET DESIGN OPTIMIZATION OPTIONS, THREADS AND TIME LIMIT FOR THE PROVE>
