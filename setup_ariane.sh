#!/bin/bash
if [ -z $DUT_ROOT ]
then
    echo "DUT_ROOT variable is empty, set it like this DUT_ROOT=<RTL_REPO_PATH> and try again"
else
    echo "Update the directories to Repos"
    echo "$DUT_ROOT"
    if [ -z $1 ]
    then
        echo "Formal Tool not selected, use [jasper | sby]"
    else
        echo "Use $1 as backend for Formal Verification"
        python autosva.py -f src/ptw.sv -x XPROP -src src/riscv-dbg/src/ -i include -tool $1
        python autosva.py -f src/tlb.sv -x XPROP -src src/riscv-dbg/src/ -i include -tool $1
        python autosva.py -f src/mmu.sv -x XPROP -src src/riscv-dbg/src/ -i include -am ptw -tool $1
    fi
fi
