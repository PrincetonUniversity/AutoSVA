# The Clear BSD License
# Copyright (c) [2021] [The Trustees of Princeton University]
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted for academic and research use only (subject to the 
# limitations in the disclaimer below) provided that the following conditions are met:
#      * Redistributions of source code must retain the above copyright notice,
#      this list of conditions and the following disclaimer.

#      * Redistributions in binary form must reproduce the above copyright
#      notice, this list of conditions and the following disclaimer in the
#      documentation and/or other materials provided with the distribution.

#      * Neither the name of the copyright holder nor the names of its
#      contributors may be used to endorse or promote products derived from this
#      software without specific prior written permission.

# NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE GRANTED BY
# THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
# CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
# PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
# CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
# PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
# BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER
# IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

import argparse
import os
import re
import sys
from shutil import copyfile
from datetime import date

#Re-generate TCL script every time we re-run autosva.py
override_tcl_script = 1
#Whether to include recursively all the directories 
#in the DUT path to include those files as possible dependencies
recursive = 0

IN = "--?IN>"
OUT = "--?OUT>"
implies = [IN, OUT]
macro = "///AUTOSVA"
# Arrays
params = []
interfaces = []
def_wires = []
assign_wires = {}
fields = {}
handshakes = {}
implications = {}
signals = {}
suffixes = {}
verbose = 0
# Default names for clock and reset signals if not found on the code parse
clk_sig = "clk"
rst_sig = "rst_n"
prop_filename_backup = ""

def get_reset():
    if "n" in rst_sig or "l" in rst_sig:
        return "!"+rst_sig
    else:
        return rst_sig
def check_size(name, sub_size, size, params):
    if sub_size and sub_size not in params:
        print("Warning: Signal '" + name + "' has a size of '" + size + "' that is not defined in this module!")

def check_interface(name, interfaces):
    if name not in interfaces:
        print("Error: '" + name + "' is not a valid interface!")
        return 1
    return 0

def check_signal(name, signals):
    if name not in signals:
        print("Error: '" + name + "' is not a valid signal!")
        return 1
    return 0

def check_annotation(annotation, line):
    if not annotation:
        print("Error: Invalid signal '" + line.replace("\n", "") + "' for annotation!")
        sys.exit(1)

def check_size_match(name, size1, size2):
    if (size1 != size2):
        print("Error: Annotation '" + name + "' has mismatched sizes! "+str(size1)+" and "+str(size2))
        return 1
    return 0

def check_id(name, entry):
    if not "p_id" in entry or not "q_id" in entry:
        print("Error: Annotation '" + name + "' is missing a main transaction ID!")
        return 1
    return 0

def check_trans_id(name, entry):
    if not "p_trans_id" in entry or not "q_trans_id" in entry:
        print("Error: Annotation '" + name + "' is missing a transaction ID!")
        return 1
    return 0

def create_dir(name):
    if (not os.path.exists(name)):
        try: 
            os.makedirs(name)
        except OSError: 
            print ("Creation of the directory %s failed" % name)
            sys.exit(1)
        else: 
            print ("Successfully created the directory %s" % name)

def parse_args():
  parser = argparse.ArgumentParser(description='AutoSVA tool for FT generation.')
  parser.add_argument("-f", "--filename", required=True, type=str, help="Path to DUT RTL module file.")
  parser.add_argument("-src", "--source", nargs="+", type=str, default=[], help="Path to source code folder where submodules are.")
  parser.add_argument("-i", "--include", type=str, help="Path to include folder that DUT and submodules use.")
  parser.add_argument("-as", "--submodule_assert", nargs="+", type=str, default=[], help="List of submodules for which ASSERT the behavior of outgoing transactions.")
  parser.add_argument("-am", "--submodule_assume", nargs="+", type=str, default=[], help="List of submodules for which ASSUME the behavior of outgoing transactions (ASSUME can constrain the DUT).")
  parser.add_argument("-x", "--xprop_macro", nargs="?", type=str, const = "NONE", help="Generate X Propagation assertions, specify argument to create property under <MACRO> (default none)")
  parser.add_argument("-tool", nargs="?", type=str, const = "sby", help="Backend tool to use [jasper|sby] (default sby)")
  parser.add_argument("-v", "--verbose", action='store_true', help="Add verbose output.")
  args = parser.parse_args()
  return args

def clean(line):
    line = line.replace("\t", "")
    while line.startswith(" "):
        line = line[1:]
    return line

def abort_tool(prop):
    print("ABORTING!")
    if not prop.closed:
        prop.close()
    copyfile(prop_filename_backup, prop.name)
    sys.exit(1)
    
def parse_annotation(line):
    global implications
    global def_wires,assign_wires

    name = None
    symbol = None

    match_in = re.search("(?:"+macro+"\s)?(\w+)\s*:\s*(\w+)\s*" + IN + "\s*(\w+)", line)
    match_out = re.search("(?:"+macro+"\s)?(\w+)\s*:\s*(\w+)\s*" + OUT + "\s*(\w+)", line)
    match_wire = re.search("(?:"+macro+"\s)?(\[.*:0\]\s+)?(\w+)\s*[=]\s*(.+)", line)

    match_trans_id = re.search(macro+" trans_id", line)
    match_trans_id_other = re.search(macro+" (trans_id_\d+)", line)
    match_trans_id_unique = re.search(macro+" trans_id_unique", line)
    match_trans_id_other_unique = re.search(macro+" (trans_id_\d+_unique)", line)
    match_data = re.search(macro+" data", line)
    
    if (verbose):  print("Parsing annotation:" + line[:-1])
    #check_annotation((match_in or match_out or match_trans_id or 
    #                match_trans_id_other or match_data or match_wire), line)
    if match_in:
        name = match_in.group(1)
        p = match_in.group(2)
        q = match_in.group(3)
        symbol = IN
    elif match_out:
        name = match_out.group(1)
        p = match_out.group(2)
        q = match_out.group(3)
        symbol = OUT
    elif match_trans_id_other_unique:
        name = match_trans_id_other_unique.group(1)
        return name
    elif match_trans_id_unique:
        return "trans_id_unique"
    elif match_trans_id_other:
        name = match_trans_id_other.group(1)
        return name
    elif match_trans_id:
        return "trans_id"
    elif match_data:
        if (verbose):  print("Matched data")
        return "data"
    elif match_wire:
        size = match_wire.group(1)
        name = match_wire.group(2)
        assign = match_wire.group(3)

        if not assign.endswith(";"):
            assign += ";"
        if size:
            wire = "wire "+size+name+";"
        else:
            wire = "wire "+name+";"

        def_wires.append(wire)
        assign_wires[name]=assign
        if (verbose):  print("Matched wire:" + wire +", assign: "+assign)
        if name.endswith("data"): parse_signal(wire,"data")
        else: parse_signal(wire,None)


    #add implications
    if symbol in implies:
        annotation = {"p": p, "q": q, "symbol": symbol, "size": "", "p_unique": None, "q_unique": None}
        implications[name] = annotation
        if (verbose):  print("Matched iface:" + p +", and: "+q)
    return None

def parse_signal(line, annotation):
    global interfaces, handshakes, signals, verbose, rst_sig, clk_sig
    name = None
    entry = None
    val = None
    rdy = None

    if (verbose):  print("Parsing signal: " + line[:-1])
    match = re.search("\s*[wire|logic|reg]?\s+(?:\[(.*):0\]\s+)?(\w+)\s*[,;=]\s*(.*)", line)
    if match:
        size = match.group(1)
        name = match.group(2)
        comment = match.group(3)
        if size is None:
            size = "0"
        else:
            size = size.replace(" ","")
        #check_size(name, sub_size, size, params)
        if (verbose):  print("Parsed signal, name: " + str(name) + 
                ", size: " + str(size) + ", com: " + str(comment))

        if name.startswith("clk"):
            clk_sig = name
        elif name.startswith("rst") or name.startswith("reset") or name.endswith("reset"):
            rst_sig = name
        #if it is a valid or ready signal      
        elif name.endswith("_val"):
            val = name.replace("_val", "")
            if val not in interfaces: # val sees first
                interfaces.append(val)
                handshakes[val] = val
            else: # got added by rdy, need to find match
                handshakes[val] = handshakes[val].replace("//", "")
        elif name.endswith("_res") or name.endswith("_rdy") or name.endswith("_ack"):
            rdy = name[0:len(name)-4]
            if rdy not in interfaces: # rdy sees first
                interfaces.append(rdy)
                handshakes[rdy] = name + "//" # yet to find matching val
            else: # got added by val
                handshakes[rdy] = name
        elif name.endswith("_trans_id") or name.endswith("_transid"):
            annotation = "trans_id"
        elif name.endswith("_trans_id_unique") or name.endswith("_transid_unique"):
            annotation = "trans_id_unique"
        # add only if the interface is defined (in implications)
        elif name.endswith("_stable"):
            annotation = "stable"
        elif name.endswith("_active"):
            key = name[:-7]
            if key in implications:
                struct = implications[key]
                if (struct): struct["active"] = name

        #if the signal was annotated
        if annotation:
            fields[name] = annotation
            if (verbose):  print("Annotated as: " + annotation)

        entry = {"size": size, "comment": comment}
        signals[name] = entry

def parse_fields(prop):
    options = "("
    list = []
    for impl_name in implications:
        entry = implications[impl_name]
        list.append(entry["p"])
        list.append(entry["q"])
    list.sort(reverse=True)
    for name in list:
        options+=name+"|"
    options+="ERROR)"

    ##fields are annotated signals
    for signal_name in fields:
        #separate iface_name and field_name (annotation)
        annotation_match = re.search(options+"_(\w+)", signal_name)
        if (check_annotation(annotation_match, signal_name)):
            abort_tool(prop)
        interface = annotation_match.group(1)
        suffix = annotation_match.group(2)
        if (verbose):  print("PF iface: " + interface + ", suffix: " + suffix)
        # Append the to interface entry of the dict, the suffix
        if (not interface in suffixes):
            suffixes[interface] = []
        suffixes[interface].append(suffix)

        #field is the type of annotation
        field = fields[signal_name]
        for impl_name in implications:
            #print("PF implication_name: " + str(impl_name));
            entry = implications[impl_name]
            if entry["p"] == interface:
                update_entry(field, impl_name, "p_", suffix)
            if entry["q"] == interface:
                update_entry(field, impl_name, "q_", suffix)

def update_entry(field, impl_name, type, suffix):
    global implications
    if (verbose):  print("UA field: " + field + ", impl_name: " + impl_name + ", type: " + type + ", suffix: " + suffix)
    entry = implications[impl_name]
    if field == "trans_id" or field == "trans_id_unique":
        entry[type + "id"] = suffix
        entry[type + field] = [suffix, ""]
    elif "trans_id" in field:
        entry[type + field] = [suffix, ""]
    elif field == "data" or field == "stable":
        entry[type + field] = suffix

    if "unique" in field:
        entry[type + field] = [suffix, ""]

    if (verbose):  print("UA: " + str(entry));

def get_sizes(prop):
    global implications,signals
    for impl_name in implications:
        entry = implications[impl_name]
        #if (check_id(impl_name, entry)): abort_tool(prop)
        if not "p_id" in entry:
            name = entry["p"]+"_transid"
            signals[name] = {"size": "'0", "comment": ""}
            entry["p_id"] = "transid"
            entry["p_trans_id"] = ["transid", ""]
        if not "q_id" in entry:
            name = entry["q"]+"_transid"
            signals[name] = {"size": "'0", "comment": ""}
            entry["q_id"] = "transid"
            entry["q_trans_id"] = ["transid", ""]
        if entry["symbol"] in implies:
            if check_interface(entry["p"], interfaces) or check_interface(entry["q"], interfaces):
                abort_tool(prop)
            for key in entry:
                keyq = key.replace("p", "q")
                if ("p_trans_id" in key) and (keyq in entry):
                    #trans_id signal suffix
                    p_trans_id = entry[key][0]
                    q_trans_id = entry[keyq][0]
                    #full signal name with iface prefix
                    p_signal_name = entry["p"] + "_" + p_trans_id
                    q_signal_name = entry["q"] + "_" + q_trans_id
                    if (verbose):  print("GS p: " + p_signal_name + ", q: " + q_signal_name);
                    #check that signals exist in signal dict
                    if check_signal(p_signal_name, signals) or check_signal(q_signal_name, `signals`):
                        abort_tool(prop)
                    #get the size of p and q trans_id from signals dict
                    size_p = signals[p_signal_name]["size"]
                    size_q = signals[q_signal_name]["size"]
                    #check that sizes match
                    if check_size_match(impl_name, size_p, size_q):
                        abort_tool(prop)
                    #update size in entries
                    entry[key][1] = size_p
                    entry[keyq][1] = size_q
                    if entry["p_id"] == p_trans_id:
                        entry["size"] = size_p
        if (verbose):  print("GS: " + str(entry));

def close_bind (module_name, bind):
    bind.write("\t\t.ASSERT_INPUTS (0)\n")
    bind.write("\t) u_" + module_name + "_sva(.*);")
    bind.close()

def gen_disclaimer(prop,rtl_file_relation):
    license_file = open(os.getcwd()+"/LICENSE", "r")
    for string in license_file:
        prop.write("// "+string)
    if rtl_file_relation:
        prop.write("// This property file was autogenerated by AutoSVA on "+str(date.today())+"\n")
        prop.write("// to check the behavior of the original RTL module, whose interface is described below: \n")
    license_file.close()
def parse_global(rtl, prop, bind):
    global params

    is_param = False
    is_signal = False
    autosva_scope = False
    parsed_module_sec = False
    parsed_disclaimer_sec = False
    module_name = "error"
    annotation = None

    for line in rtl:
        line = clean(line)
        #Show the parsed line if verbose mode
        if (verbose):  print("Parsing global:" + line[:-1])

        if line.startswith("module"):
            if not parsed_disclaimer_sec:
                parsed_disclaimer_sec = True
                gen_disclaimer(prop,True)
            parsed_module_sec = True
            matches = re.search("module\s+(\w+)(.*)", line)
            module_name = matches.group(1)
            print("Module name:" + module_name)
            rest = matches.group(2)
            prop.write("module " + module_name + "_prop\n")
            gen_disclaimer(bind,False)
            bind.write("bind " + module_name + " " + module_name + "_prop\n")
            bind.write("\t#(\n")
            if "#(" in rest:
                is_param = True
                prop.write(rest+"\n\t\tparameter ASSERT_INPUTS = 0,\n")
            elif "(" in rest:
                prop.write("#(\n\t\tparameter ASSERT_INPUTS = 0)\n"+rest+"\n")
                is_signal = True
                close_bind(module_name,bind)

        elif (is_param and (not is_signal)) or (parsed_module_sec and line.startswith("#(")):
            if line.startswith("#("):
                is_param = True
                line = line[2:]
                prop.write("#(\n\t\tparameter ASSERT_INPUTS = 0,\n")
            if "parameter" in line:
                prop.write("\t\t" + line)
                matches = re.findall("\s*\t*parameter\s+(\w+)\s+=\s*\d+(?:,)?", line)
                for param in matches:
                    bind.write("\t\t." + param + " (" + param + "),\n")
                    params.append(param)
            #when param section contains the close symbol
            elif line.startswith(")"):
                prop.write(line)
                is_signal = True
                close_bind(module_name,bind)
            #else:
            #    print("Wrong format in parameter section! Expecting parameter or )")

        elif is_signal or (parsed_module_sec and line.startswith("(")):
            if line.startswith("("):
                if not is_signal:
                    is_signal = True
                    close_bind(module_name,bind)
                if (not is_param):
                    prop.write("#(\n\t\tparameter ASSERT_INPUTS = 0)\n(\n")
                else:
                    prop.write("(")
            elif line.startswith("/*AUTOSVA"):
                autosva_scope = True
            elif line.startswith("*/"):
                autosva_scope = False
            elif line.startswith(macro) or autosva_scope: # annotation
                annotation = parse_annotation(line)
            else:
                if line.startswith(");"):
                        parse_fields(prop)
                        get_sizes(prop)
                        prop.write("\t" + line)
                        prop.write("\n")
                        prop.write("//==============================================================================\n")
                        prop.write("// Local Parameters\n")
                        prop.write("//==============================================================================\n\n")
                        break
                if line.startswith("output"): # output wire
                    line = line.replace("output", "input ").split("\n")[0]
                    line += " //output\n"
                    prop.write("\t\t" + line)
                    parse_signal(line[5:], annotation)
                elif line.startswith("input"):
                    prop.write("\t\t" + line)
                    parse_signal(line[5:], annotation)
                elif line.startswith("wire"):
                    prop.write("\t\tinput  " + line)
                    parse_signal(line, annotation)
                else:
                    prop.write("\t\t" + line)
                annotation = None

        elif not parsed_module_sec:
            if (not parsed_disclaimer_sec) and (not line.startswith("//")):
                parsed_disclaimer_sec = True
                gen_disclaimer(prop,True)
            if parsed_disclaimer_sec:
                prop.write(line)
        else:
            print("Wrong RTL formal, module header parsed but failed to parse the rest")
            sys.exit(1)

def gen_vars(tool, prop):
    prop.write("genvar j;\ndefault clocking cb @(posedge " + clk_sig + ");\nendclocking\ndefault disable iff (" + get_reset() + ");\n")
    if tool == "sby":
        prop.write("reg reset_r = 0;\n")
        prop.write("am__rst: assume property (reset_r != "+get_reset()+");\n")
        prop.write("always_ff @(posedge clk_i)\n")
        prop.write("    reset_r <= 1'b1;\n")
    prop.write("\n// Re-defined wires \n")
    # Keep track of the wires already defined for symbolics and handshakes
    def_symb_hsk = []
    for line in def_wires:
        prop.write(line+"\n")
    prop.write("\n// Symbolics and Handshake signals\n")
    for impl_name in implications:
        entry = implications[impl_name]
        for key in entry:
            if "p_trans_id" in key and key.replace("p", "q") in entry:
                if (verbose):  print("GenVAR:" + impl_name +", key "+key)
                trans_id_entry = entry[key]
                size = trans_id_entry[1]
                symb_name = "symb_" + entry["p"] + "_" + trans_id_entry[0]
                if size != "'0" and (not symb_name in def_symb_hsk):
                    prop.write("wire [" + size + ":0] " + symb_name + " = 'x;\n")
                    prop.write("am__" + symb_name + "_stable: assume property($stable(" + symb_name + "));\n")
                    def_symb_hsk.append(symb_name)
            elif key == "p" or key == "q":
                interface = entry[key]
                handshake = handshakes[interface]
                if handshake.endswith("//"): # skip those that never found matching val
                    continue
                # Define Handshake wire
                base = handshake
                wire_def = base + "_hsk"
                if interface != handshake: # valid and ready
                    base = handshake[0:len(handshake)-4]
                    wire_def = base + "_hsk"
                    
                # Check if the wire was defined already
                if not wire_def in def_symb_hsk:
                    def_symb_hsk.append(wire_def)
                    if interface != handshake:
                        prop.write("wire " + base + "_hsk = " + base + "_val && " + handshake + ";\n")
                    else: # Valid without a matching ready
                        prop.write("wire " + wire_def + " = " + base + "_val;\n")
          
    prop.write("\n")

def gen_models(prop):
    prop.write("//==============================================================================\n")
    prop.write("// Modeling\n")
    prop.write("//==============================================================================\n\n")
    for iface_name in implications:
        entry = implications[iface_name]
        if entry["symbol"] == IN:
            gen_in(prop, iface_name, entry)
        elif entry["symbol"] == OUT:
            gen_out(prop, iface_name, entry)

        for key in entry:
            if key.startswith("p") and "unique" in key and key.replace("p", "q") in entry:
                if entry[key] and entry[key.replace("p", "q")]:
                    gen_unique(prop, iface_name, entry, entry[key], entry[key.replace("p", "q")])

def gen_in(prop, name, entry):
    p = entry["p"]
    q = entry["q"]
    size = entry["size"]
    if (verbose): 
        print("GenIN:" + name)

    prop.write("// Modeling incoming request for " + name + "\n")
    if q != handshakes[q]: # has ready signal, not equal to interface name
        # the external module eventually accepts the response
        prop.write("if (ASSERT_INPUTS) begin\n")
        prop.write("\tas__" + name + "_fairness: assert property (" + q + "_val |-> s_eventually(" + handshakes[q] + "));\n")
        prop.write("end else begin\n")
        prop.write("\tam__" + name + "_fairness: assume property (" + q + "_val |-> s_eventually(" + q + "_rdy));\n")
        prop.write("end\n\n")

    key = "p_trans_id"; keyq = "q_trans_id"
    if key in entry and keyq in entry:
        name_tid = name + "_" +entry[key][0]
        p_trans_id = p + "_" + entry[key][0]
        q_trans_id = q + "_" + entry[keyq][0]
        symb_name = "symb_" + p_trans_id
        
        if (verbose):  print("GenIN Trans:" + p_trans_id)
        prop.write("// Generate sampling signals and model\n")
        count = 1
        if not "unique" in key:
            count = 3 #count_log-1
        gen_iface_sampled(prop, name_tid, p, q, p_trans_id, q_trans_id, symb_name, entry, count,size)
        
        # Generate Stability Assumptions
        # If stable then assume payload is stable and valid is non-dropping
        if p != handshakes[p] and "p_stable" in entry:
            prop.write("// Assume payload is stable and valid is non-dropping\n")
            prop.write("if (ASSERT_INPUTS) begin\n")
            prop.write("\tas__" + name_tid + "_stability: assert property (" + p + "_val && !" + handshakes[p] + " |=> "+ p +"_val && $stable(" + p + "_" + entry["p_stable"] + ") );\n")  
            prop.write("end else begin\n")
            prop.write("\tam__" + name_tid + "_stability: assume property (" + p + "_val && !" + handshakes[p] + " |=> "+ p +"_val && $stable(" + p + "_" + entry["p_stable"] + ") );\n")  
            prop.write("end\n\n")
            
        # Otherwise assert that if valid eventually ready or dropped valid
        if p != handshakes[p]:
            prop.write("// Assert that if valid eventually ready or dropped valid\n")
            prop.write("as__" + name_tid + "_hsk_or_drop: assert property (" + p + "_val |-> s_eventually(!" + p + "_val || "+handshakes[p]+"));\n")
        # Assert liveness!
        prop.write("// Assert that every request has a response and that every reponse has a request\n")
        prop.write("as__" + name_tid + "_eventual_response: assert property (" + name_tid + "_set |-> s_eventually(" + q + "_val")
        if size != "'0": prop.write(" && (" + q_trans_id + " == " + symb_name + ") ));\n")
        else: prop.write("));\n")
        prop.write("as__" + name_tid + "_was_a_request: assert property (" + name_tid + "_response |-> "+name_tid+"_set || "+name_tid+"_sampled);\n\n")
    if "p_data" in entry and "q_data" in entry:
        p_trans_id = p + "_" + entry["p_id"]
        q_trans_id = q + "_" + entry["q_id"]
        name_tid = name + "_" + entry["p_id"]
        p_data = p + "_" + entry["p_data"]
        q_data = q + "_" + entry["q_data"]
        symb_name = "symb_" + p_trans_id
        data_integrity(prop, name_tid, p, q, p_trans_id, q_trans_id, p_data, q_data, symb_name, size)

def gen_iface_sampled (prop, name, p, q, p_trans_id, q_trans_id, symb_name, entry, count,size):
    prop.write("reg ["+str(count)+":0] " + name + "_sampled;\n")
    prop.write("wire " + name + "_set = " + p + "_hsk")
    if size != "'0": prop.write(" && " + p_trans_id + " == " + symb_name + ";\n")
    else: prop.write(";\n")
    prop.write("wire " + name + "_response = " + q + "_hsk")
    if size != "'0": prop.write(" && " + q_trans_id + " == " + symb_name + ";\n\n")
    else: prop.write(";\n\n")

    prop.write("always_ff @(posedge " + clk_sig + ") begin\n")
    prop.write("\tif(" + get_reset() + ") begin\n")
    prop.write("\t\t" + name + "_sampled <= '0;\n")
    prop.write("\tend else if (" + name + "_set || "+ name + "_response ) begin\n")
    prop.write("\t\t"+name+"_sampled <= "+name+"_sampled + "+name+"_set - "+name+"_response;\n")
    prop.write("\tend\n")
    prop.write("end\n")
    # do not create sampled cover if it's never going to be sampled
    p_rdy = p+"_rdy";
    p_val = q+"_val"
    if not ((p_rdy in assign_wires) and (p_val in assign_wires) and (assign_wires[p_rdy] == assign_wires[p_val]) ):
        prop.write("co__" + name + "_sampled: cover property (|" + name + "_sampled);\n")
    if count > 0: # When not unique assume that this sampling structure would not overflow
        prop.write("if (ASSERT_INPUTS) begin\n")
        prop.write("\tas__" + name + "_sample_no_overflow: assert property ("+name+"_sampled != '1 || !"+name+"_set);\n")
        prop.write("end else begin\n")
        prop.write("\tam__" + name + "_sample_no_overflow: assume property ("+name+"_sampled != '1 || !"+name+"_set);\n")
        prop.write("end\n\n")
        
    if "active" in entry:
        prop.write("as__" + name + "_active: assert property (" + name + "_sampled > 0 |-> "+entry["active"]+");\n\n")
    else:
        prop.write("\n")

def data_integrity(prop, name, p, q, p_trans_id, q_trans_id, p_data, q_data, symb_name, size):
    size_p = signals[p_data]["size"]

    prop.write("\n// Modeling data integrity for " + name + "\n")
    prop.write("reg [" + size_p + ":0] " + name + "_data_model;\n")
    prop.write("always_ff @(posedge " + clk_sig + ") begin\n")
    prop.write("\tif(" + get_reset() + ") begin\n")
    prop.write("\t\t" + name + "_data_model <= '0;\n")
    prop.write("\tend else if (" + name + "_set) begin\n")
    prop.write("\t\t" + name + "_data_model <= " + p_data + ";\n")
    prop.write("\tend\n")
    prop.write("end\n\n")
    
    prop.write("as__" + name + "_data_integrity: assert property (" + name + "_sampled && " + q + "_hsk ");
    if size != "'0": prop.write(" && (" +q_trans_id + " == " + symb_name + ")"); 
    prop.write("|-> (" + q_data + " == " + name + "_data_model));\n\n");

def gen_out(prop, name, entry):
    p = entry["p"]
    q = entry["q"]
    size = entry["size"]
    p_trans_id = p + "_" + entry["p_id"]
    q_trans_id = q + "_" + entry["q_id"]
    p_data = None
    if "p_data" in entry and "q_data" in entry:
        p_data = p + "_" + entry["p_data"]
        q_data = q + "_" + entry["q_data"]
        size_p = signals[p_data]["size"]

    symb_name = "symb_" + p_trans_id
    if (size == "'0"):
        power_size = "1"
    else:
        power_size = "2**("+ size + "+1)"
    prop.write("// Modeling outstanding request for " + name + "\n")
    prop.write("reg [" + power_size + "-1:0] " + name + "_outstanding_req_r;\n")
    if p_data:
        prop.write("reg [" + power_size + "-1:0]["+size_p+":0] " + name + "_outstanding_req_data_r;\n")
    prop.write("\n")
    prop.write("always_ff @(posedge " + clk_sig + ") begin\n")
    prop.write("\tif(" + get_reset() + ") begin\n")
    prop.write("\t\t" + name + "_outstanding_req_r <= '0;\n")
    prop.write("\tend else begin\n")
    prop.write("\t\tif (" + p + "_hsk) begin\n")
    if size == "'0":
        prop.write("\t\t\t" + name + "_outstanding_req_r <= 1'b1;\n")
    else:
        prop.write("\t\t\t" + name + "_outstanding_req_r[" + p_trans_id + "] <= 1'b1;\n")
    if p_data:
        if size == "'0":
            prop.write("\t\t\t" + name + "_outstanding_req_data_r <= "+p_data+";\n")
        else:
            prop.write("\t\t\t" + name + "_outstanding_req_data_r[" + p_trans_id + "] <= "+p_data+";\n")
    prop.write("\t\tend\n")
    prop.write("\t\tif (" + q + "_hsk) begin\n")
    if size == "'0":
        prop.write("\t\t\t" + name + "_outstanding_req_r <= 1'b0;\n")
    else:
        prop.write("\t\t\t" + name + "_outstanding_req_r[" + q_trans_id + "] <= 1'b0;\n")
    prop.write("\t\tend\n")
    prop.write("\tend\n")
    prop.write("end\n")
    prop.write("\n")
    if "active" in entry:
        prop.write("as__" + name + "_active: assert property (|" + name + "_outstanding_req_r |-> "+entry["active"]+");\n\n")
    else:
        prop.write("\n")

    prop.write("generate\n")
    # First Assertion (if macro defined)
    prop.write("if (ASSERT_INPUTS) begin : " + name+ "_gen\n")
    if size == "'0":
        prop.write("\tas__" + name + "1: assert property (!" + name + "_outstanding_req_r |-> !(" + q + "_hsk));\n")
    else:
        prop.write("\tas__" + name + "1: assert property (!" + name + "_outstanding_req_r[" + symb_name + "] ")
        prop.write("|-> !(" + q + "_hsk && (" + q_trans_id + " == " + symb_name + ")));\n")
    
    # Second assertion
    if size == "'0":
        prop.write("\tas__" + name + "2: assert property (" + name + "_outstanding_req_r |-> s_eventually(" + q + "_hsk")
    else:
        prop.write("\tas__" + name + "2: assert property (" + name + "_outstanding_req_r[" + symb_name + "] ")
        prop.write("|-> s_eventually(" + q + "_hsk && (" + q_trans_id + " == " + symb_name + ")")
    if p_data:
        if size == "'0":
            prop.write("&&\n\t (" + q_data + " == " + name + "_outstanding_req_data_r) ));\n")
        else:
            prop.write("&&\n\t (" + q_data + " == " + name + "_outstanding_req_data_r[" + symb_name + "]) ));\n")
    else:
        prop.write("));\n")
    prop.write("end else begin : " + name+ "_else_gen\n")
    
    if p != handshakes[p]:
        prop.write("\tam__" + name + "_fairness: assume property (" + p + "_val |-> s_eventually(" + p + "_rdy));\n")
    prop.write("\tfor ( j = 0; j < " + power_size + "; j = j + 1) begin : " + name+ "_for_gen\n")
    prop.write("\t\tco__" + name + ": cover property (" + name + "_outstanding_req_r[j]);\n")
    # First Assertion
    prop.write("\t\tam__" + name + "1: assume property (!" + name + "_outstanding_req_r[j] ")
    if size == "'0":
        prop.write("|-> !(" + q + "_val));\n")
    else:
        prop.write("|-> !(" + q + "_val && (" + q_trans_id + " == j)));\n")
        
    # Second Assertion
    prop.write("\t\tam__" + name + "2: assume property (" + name + "_outstanding_req_r[j] ")
    if size == "'0":
        prop.write("|-> s_eventually(" + q + "_val")
    else:
        prop.write("|-> s_eventually(" + q + "_val && (" + q_trans_id + " == j)")
    if p_data:
        prop.write("&&\n\t (" + q_data + " == " + name + "_outstanding_req_data_r[j]) ));\n")
    else:
        prop.write("));\n")
    prop.write("\tend\n")
    prop.write("end\n")
    prop.write("endgenerate\n")
    prop.write("\n")

def gen_unique(prop, name, entry, p_key, q_key):
    p = entry["p"]
    q = entry["q"]
    p_trans_id = p + "_" + p_key[0]
    q_trans_id = q + "_" + q_key[0]
    size = p_key[1]
    symb_name = "symb_" + p_trans_id
    power_size = "2**("+ size + "+1)"
    prop.write("// Max 1 outstanding request for " + name + "\n")
    prop.write("reg [" + power_size + "-1:0] " + name + "_unique_outstanding_req_r;\n")
    prop.write("wire " + name + "_equal = " + p_trans_id + " == " + q_trans_id + ";\n")
    prop.write("\n")
    prop.write("always_ff @(posedge " + clk_sig + ") begin\n")
    prop.write("\tif(" + get_reset() + ") begin\n")
    prop.write("\t\t" + name + "_unique_outstanding_req_r <= '0;\n")
    prop.write("\tend else begin\n")
    prop.write("\t\tif (" + p + "_hsk) begin\n")

    prop.write("\t\t\t" + name + "_unique_outstanding_req_r[" + p_trans_id + "] <= 1'b1;\n")
    prop.write("\t\tend\n")
    prop.write("\t\tif (" + q + "_hsk) begin\n")
    prop.write("\t\t\t" + name + "_unique_outstanding_req_r[" + q_trans_id + "] <= 1'b0;\n")
    prop.write("\t\tend\n")
    prop.write("\tend\n")
    prop.write("end\n")
    prop.write("\n")

    prop.write("generate\n")
    prop.write("if (ASSERT_INPUTS) begin : " + name+ "_gen\n")
    prop.write("\tas__" + name + "_unique: assert property (" + name + "_unique_outstanding_req_r[" + symb_name + "] ")
    prop.write("|-> !(" + p + "_hsk && (" + p_trans_id + " == " + symb_name + ")));\n")
    prop.write("end else begin : " + name+ "_else_gen\n")
    prop.write("\tfor ( j = 0; j < " + power_size + "; j = j + 1) begin : " + name+ "_for_gen\n")
    prop.write("\t\tam__" + name + "_unique: assume property (" + name + "_unique_outstanding_req_r[j] ")
    prop.write("|-> !(" + p + "_val && (" + p_trans_id + " == j)));\n")
    prop.write("\tend\n")
    prop.write("end\n")
    prop.write("endgenerate\n")
    prop.write("\n")

    prop.write("as__" + name + "_unique1: assert property(" + name + "_unique_outstanding_req_r[" + symb_name + "] ")
    prop.write("|-> s_eventually(" + q + "_hsk && (" + q_trans_id + " == " + symb_name + ")));\n")
    prop.write("\n")

def link_submodules(submodule_assert,submodule_assume):
    files = []
    # Add binding of submodules
    base = os.getcwd()+"/ft_"
    basev = "${AUTOSVA_ROOT}/ft_"
    for sub_name in submodule_assume:
        file_prop = sub_name+"/sva/"+sub_name+"_prop.sv"
        file_bind = sub_name+"/sva/"+sub_name+"_bind.svh"
        if os.path.exists(base+file_prop) and os.path.exists(base+file_bind):
            files.append(basev+file_prop+"\n")
            files.append(basev+file_bind+"\n") 
    for sub_name in submodule_assert:
        file_prop = sub_name+"/sva/"+sub_name+"_prop.sv"
        file_bind = sub_name+"/sva/"+sub_name+"_bind.svh"
        if os.path.exists(base+file_prop) and os.path.exists(base+file_bind):
            files.append(basev+file_prop+"\n")
            new_bind = dut_name+"/sva/"+sub_name+"_bind.svh"
            files.append(basev+new_bind+"\n") 
            # Write the new binding file from the old one
            old_bind_file = open(base+file_bind, "r")
            new_bind_file = open(base+new_bind, "w+")
            for line in old_bind_file:
                line = line.replace("INPUTS (0)", "INPUTS (1)")
                new_bind_file.write(line)
            old_bind_file.close()
            new_bind_file.close()
    return files

def gen_tcl(dut_root,ft_path, dut_folder, src_list, include, dut_name, dut_name_ext, submodule_assert, submodule_assume):
    global clk_sig, rst_sig
    vc_filename = ft_path + "files.vc"
    tcl_filename = ft_path + "FPV.tcl"

    if (not os.path.exists(tcl_filename) or override_tcl_script):
        tcl = open(tcl_filename, "w+")
        tcl.write("# THIS FILE IS A PLACEHOLDER, WHERE YOU WOULD NEED TO INCLUDE THE RIGHT COMMANDS\n")
        tcl.write("# OF JASPERGOLD ONCE YOU ADQUIRE A LICENSE AND HAVE ACCESS TO THE TOOL DOCUMENTATION\n\n")
        tcl.write("# Set paths to DUT root and FT root (edit if needed)\n")
        tcl.write("set DUT_ROOT "+dut_root+"\n")
        tcl.write("set AUTOSVA_ROOT "+ft_path+"..\n\n")
        tcl.write("# Analyze design under verification files (no edit)\n")
        tcl.write("set DUT_PATH ${DUT_ROOT}/"+dut_folder+"\n")
        if src_list: 
            index = 0
            for src_folder in src_list:
                tcl.write("set SRC_PATH"+str(index)+" ${DUT_ROOT}/"+src_folder+"\n")
                index+=1
        if include: tcl.write("set INC_PATH ${DUT_ROOT}/"+include+"\n")
        tcl.write("set PROP_PATH ${AUTOSVA_ROOT}/ft_"+dut_name+"/sva\n\n")
        tcl.write("# Include property and RTL files\n")
        tcl.write("<USE COMMAND TO INCLUDE FILES AT> ${AUTOSVA_ROOT}/ft_"+dut_name+"/files.vc\n\n")
        tcl.write("# Build design and properties\n")
        tcl.write("<BUILD USING THIS MODULE AS TOP> " + dut_name + "\n\n")
        tcl.write("# Set up Clocks and Resets\n")
        tcl.write("<SET CLOCK SIGNAL> "+clk_sig+"\n")
        tcl.write("<SET RESET SIGNAL> "+get_reset()+")\n\n")
        tcl.write("# Tool options, run and report proof results\n")
        tcl.write("<SET DESIGN OPTIMIZATION OPTIONS, THREADS AND TIME LIMIT FOR THE PROVE>\n")
        tcl.close()

    if (not os.path.exists(vc_filename) or override_tcl_script):
        vc = open(vc_filename, "w+")
        vc.write("<ADD RTL FILE EXTENSIONS>\n")
        vc.write("<INCLUDE>${DUT_PATH}\n")
        if src_list: 
            index = 0
            for src_folder in src_list:
                string = "SRC_PATH"+str(index)
                index+=1
                vc.write("<INCLUDE> ${"+string+"}\n")
                for root, subdirs, files in os.walk(src_folder):
                    if (verbose):  print("--"+string+" = " + root)
                    vc.write("<INCLUDE> "+root+"\n")
                       
        if include:
            vc.write("<INCLUDE>${INC_PATH}\n") 
        vc.write("${PROP_PATH}/"+ dut_name + "_prop.sv\n") 
        vc.write("${PROP_PATH}/"+ dut_name + "_bind.svh\n") 

        for line in link_submodules(submodule_assert,submodule_assume):
            vc.write(line)
        vc.write("${DUT_ROOT}/"+dut_folder+ dut_name+"."+dut_name_ext.split(".")[1]+"\n"); 
        vc.close()

def gen_sby(dut_root, ft_path, dut_folder, src_list, include, dut_name, dut_name_ext, submodule_assert, submodule_assume):
    global clk_sig, rst_sig
    sby_filename = ft_path + "FPV.sby"
    sva_path = ft_path+"sva"

    if (not os.path.exists(sby_filename)):
        sby = open(sby_filename, "w+")
        sby.write("[tasks]\n")    
        sby.write("cvr\n")
        sby.write("prv\n")
        #sby.write("live\n\n")
        sby.write("[options]\n")    
        sby.write("cvr: mode cover\n")
        sby.write("prv: mode prove\n")
        #sby.write("live: mode live\n")
        #sby.write("depth 100\n\n")
        sby.write("[engines]\n")
        sby.write("cvr: smtbmc z3\n")
        sby.write("prv: abc pdr\n")
        #sby.write("live: aiger suprove\n\n")
        sby.write("[script]\n")
        sby.write("read -verific\n");
        # Link submodule property and bind files
        link_files = link_submodules(submodule_assert,submodule_assume)
        for line in link_files:
            strings = line.split("/")
            sby.write("read -sv "+strings[len(strings)-1])
        # Add other file dependencies
        if not recursive:
            # Only explicitely add the DUT top when it will not be added in the recursive search
            dut_full_name = dut_name+"."+dut_name_ext.split(".")[1]
            sby.write("read -sv "+dut_full_name+"\n");
        else:
            file_list = []
            read_list = []
            if src_list: src_list.append(dut_folder)
            else: src_list = [dut_folder]
            if include:
                src_list.insert(0, include)
            for src_folder in src_list:
                abs_path = dut_root+"/"+src_folder
                len_dut_root = len(dut_root)
                print(abs_path)
                for root, subdirs, files in os.walk(abs_path):
                    rel_path = "$DUT_ROOT"+root[len_dut_root:]
                    if (verbose): print("--"+src_folder+" = " + rel_path)
                    for name in files:
                        if name.endswith(".sv") or name.endswith(".v"):
                            file_list.append(rel_path+"/"+name)
                            read_list.append(name)
            for filename in read_list: sby.write("read -sv "+filename+"\n")

        sby.write("read -sv "+dut_name+"_prop.sv\n")
        sby.write("read -sv "+dut_name+"_bind.svh\n")
        sby.write("prep -top "+dut_name+"\n\n");
        sby.write("[files]\n")

        for line in link_files:
            sby.write(line)
        sby.write("$AUTOSVA_ROOT/ft_"+dut_name+"/sva/"+ dut_name + "_prop.sv\n")
        sby.write("$AUTOSVA_ROOT/ft_"+dut_name+"/sva/"+ dut_name + "_bind.svh\n")
        if not recursive:
            # No need to explicitely add the DUT top since it will be added in the recursive search
            sby.write("$DUT_ROOT/"+dut_folder+dut_full_name+"\n");
        else:
            for filename in file_list: sby.write(filename+"\n")
        sby.close()

def parse_former_prop(prop, prop_backup):
    former_sva = []
    save = False
    for orig_line in prop:
        prop_backup.write(orig_line)
        if (not save):
            line = clean(orig_line)
            if line.startswith("//====DESIGNER-ADDED-SVA====//"):
                save = True
        else:
            former_sva.append(orig_line)
            if (verbose):  print("Saving former designer SVA: " + orig_line)
    return former_sva

        
def autosva_main():
    # Variable declaration
    global verbose, prop_filename_backup
    former_sva = ["endmodule"]

    # Extract arguments
    args = parse_args()
    verbose = args.verbose
    src_list = args.source
    include = args.include
    submodule_assert = args.submodule_assert
    submodule_assume = args.submodule_assume
    dut_folder = args.filename
    xprop = args.xprop_macro
    tool = args.tool
    # Get absolute Paths
    dut_root = os.getenv('DUT_ROOT')
    if not dut_root:
        print("You must define DUT_ROOT")
        sys.exit(1)
    autosva_root = os.getenv('AUTOSVA_ROOT')
    if not autosva_root:
        print("You must define AUTOSVA_ROOT")
        sys.exit(1)
    if not os.path.exists(os.getcwd()+"/LICENSE"):
        print("Please run the script from the root folder of the repository where the LICENSE file is")
        sys.exit(1)
    dut_path = os.path.abspath(dut_root+"/"+dut_folder)

    # Parse DUT folder and name
    dut_name = os.path.basename(dut_path).split(".")[0]
    # Create FT folder and SVA folder inside it
    ft_path = os.getcwd()+"/ft_"+dut_name+"/"
    create_dir(ft_path)
    sva_path = ft_path + "sva/"
    create_dir(sva_path)
    dut_folder = dut_folder.split(".")[0]
    dut_folder = dut_folder[0:-len(dut_name)]

    # Property and Bind files
    prop_filename = sva_path + dut_name + "_prop.sv"
    prop_filename_backup = sva_path + dut_name + "_prop_old.sv"
    bind_filename = sva_path + dut_name + "_bind.svh"
    if (os.path.exists(prop_filename)):
        #extract handwritten properties to the previous prop file
        prop_old = open(prop_filename, "r+")
        prop_backup = open(prop_filename_backup, "w+")
        former_sva = parse_former_prop(prop_old, prop_backup)
        prop_old.close()
        prop_backup.close()

    # Open files RTL, Bind, Property  files
    rtl = open(dut_path, "r+")
    prop = open(prop_filename, "w+")
    bind = open(bind_filename, "w+")

    # Parse header file and generate SVA
    parse_global(rtl, prop, bind)
    gen_vars(tool,prop)
    gen_models(prop)

    # Add the new write assignments
    for key in assign_wires:
        prop.write("assign "+key+" = "+assign_wires[key]+"\n")
    #define macro for simulation if needed
    if (xprop):
        prop.write("\n//X PROPAGATION ASSERTIONS\n")
        if xprop != "NONE":
            prop.write("`ifdef "+xprop+"\n")
        for iface_name in suffixes:
            valid_name = iface_name+"_val"
            prop.write("\t as__no_x_"+valid_name+": assert property(!$isunknown("+valid_name+"));\n")
            iface_list = suffixes[iface_name]
            for suffix in iface_list:
                signal_name = iface_name+"_"+suffix
                prop.write("\t as__no_x_"+signal_name+": assert property("+valid_name+" |-> !$isunknown("+signal_name+"));\n")
        if xprop != "NONE":
            prop.write("`endif\n")

    prop.write("\n//====DESIGNER-ADDED-SVA====//\n")
    # Add handwritten SVA properties extracted from old version of prop file
    for line in former_sva:
        prop.write(line)

    # Close RTL and Property files
    rtl.close()
    prop.close()

    # Write VC (path file) and TCL (command file)
    if tool == "sby":
        gen_sby(dut_root, ft_path, dut_folder, src_list, include, dut_name, dut_path, submodule_assert, submodule_assume)
    else:
        gen_tcl(dut_root,ft_path, dut_folder, src_list, include, dut_name, dut_path, submodule_assert, submodule_assume)

autosva_main()