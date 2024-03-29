# Set paths to DUT root and FT root (based on environment variables)
set AUTOSVA_ROOT $env(AUTOSVA_ROOT)
set DUT_ROOT $env(DUT_ROOT)

# Analyze design under verification files (no edit)
set DUT_PATH ${DUT_ROOT}/
set PROP_PATH ${AUTOSVA_ROOT}/ft_fifo/sva

set_elaborate_single_run_mode off
set_automatic_library_search on
set_analyze_libunboundsearch on
set_analyze_librescan on
# Analyze property files
analyze -clear
analyze -sv12 -f ${AUTOSVA_ROOT}/ft_fifo/files.vc
# Elaborate design and properties
elaborate -top fifo -create_related_covers {witness precondition} -auto_hr_info
# Set up Clocks and Resets
clock clk
reset -expression (!rst_n)

# Get design information to check general complexity
get_design_info

set_word_level_reduction on
set_prove_time_limit 72h

set_proofgrid_max_jobs 180
set_proofgrid_manager on
autoprove -all -bg
# Report proof results
report
