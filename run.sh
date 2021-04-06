#!/bin/bash
if [ -z "$1" ]
then
    echo "DUT param is empty, use ./run.sh <DUT> (without .v)"
else
    sby ft_$1/FPV.sby -f
fi