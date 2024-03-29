
Steps to setup a couple of Formal Testbenches (FT) for the imuldiv module for Course COS/ECE 475/575

- Create a fork of this repo https://github.com/PrincetonUniversity/AutoSVA
- Create a new private repo in your github account and add me as a collaborator @morenes
- Push the content of this repo to your new private repo

Add these to your .bashrc
        export DUT_ROOT=/home/YOUR_USER/AutoSVA
        export AUTOSVA_ROOT=$DUT_ROOT

- Copy over the imuldiv folder from the ele475-lab2 (the solutions) to AUTOSVA_ROOT


Add these annotations to the imuldiv-IntMulDivIterative file

        module imuldiv_IntMulDivIterative
        (
        /*AUTOSVA
        trans: muldivreq -IN> muldivresp
        */
        input         clk,
        input         reset,

Only the first time you create a Formal Testbench (FT), here for IntMulDivIterative. Note the annotations in imuldiv-IntMulDivIterative.v

        python autosva.py -f ele475-lab2/imuldiv/imuldiv-IntMulDivIterative.v -v -i ele475-lab2/imuldiv -x XPROP -tool jasper

Run the Testbench created
        source run_jg.sh imuldiv-IntMulDivIterative



Add these annotations to the imuldiv_IntMulIterative file

        module imuldiv_IntMulIterative
        (
        /*AUTOSVA
        mulreq_trans: mulreq -IN> mulresp
        [63:0] mulreq_data = mulreq_msg_a * mulreq_msg_b
        mulreq_transid = 1'b0
        [63:0] mulresp_data = mulresp_msg_result
        mulresp_transid = 1'b0
        */
        input                clk,
        input                reset,

Create a Formal Testbench (FT) for IntMulIterative, note the annotations in imuldiv-IntMulIterative.v

        python autosva.py -f ele475-lab2/imuldiv/imuldiv-IntMulIterative.v -v -i ele475-lab2/imuldiv -x XPROP -tool jasper
        source run_jg.sh imuldiv-IntMulIterative

In the newly created ft_imuldiv-IntMulIterative testbench you need to add more properties in the sva/*_prop.sv files!
To create properties you may use some help from this GPT agent:
https://chat.openai.com/g/g-5CfYpl72L-autosva