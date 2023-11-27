/*
RULES:
AutoSVA is a tool that generates SVA assertions for RTL module transactions.
The SVA assertions are written from the perspective of the RTL module that is the design-under-test (DUT).
An RTL module has input and output signals in the module interface.
Groups of signals in the module interface are called interfaces.
Pairs of interfaces denote transactions: a transaction connects a request interface to a response interface.
A request interface can be output by the DUT (outgoing transations), and so a response is expected to be received by the DUT eventually via an input reponse interface.
A request interface can be an input to the DUT (incoming transations), and so a response is expected to be sent by the DUT eventually via an output reponse interface.
AutoSVA requires annotations into the signal declaration section of the module interface to identify the interfaces and transactions.
The annotations are written as a multi-line Verilog comment starting with /*AUTOSVA 
A transation is defines as: transaction_name: request_interface -IN> response_interface if it's an incoming transaction. Thus the request interface is the input interface and the response interface is the output interface.
A transation is alternatively defined as: transaction_name: request_interface -OUT> response_interface if it's an outgoing transaction. Thus the request interface is the output interface and the response interface is the input interface.
For example, the following FIFO module interface has an incoming transaction called fifo_transaction: push -IN> pop
module fifo (
input  wire             push_val,
output wire             push_rdy,
input  wire [WIDTH-1:0] push_payload,
output wire             pop_val,
input  wire             pop_rdy,
output wire [WIDTH-1:0] pop_payload
);
and so the AUTOSVA annotation is:
/*AUTOSVA
fifo_transaction: push -IN> pop
                    push_valid = push_val
                    push_ready = push_rdy
[WIDTH-1:0]         push_data = push_payload
[INFLIGHT_IDX-1:0]  push_transid = fifo.write_pointer
                    pop_valid = pop_val
                    pop_ready = pop_rdy
[WIDTH-1:0]         pop_data = pop_payload
[INFLIGHT_IDX-1:0]  pop_transid = fifo.read_pointer

NOTE that in addition to the fifo_transaction: push -IN> pop there are more annotations that match interface signals with interface atributes.
Both request and response interfaces have valid, ready, data and transid attributes.
Valid indicates that the request or response is valid, and can be acknowledged by the other side.
Ready indicates that the request or response is ready to be received by the other side.
Data is the payload of the request or response.
Transid is a unique identifier of the request or response.

The formalized syntax of the AUTOSVA annotation is:
TRANSACTION ::= TNAME: RELATION ATTRIB
RELATION ::= P −in> Q | P −out> Q
ATTRIB ::= ATTRIB, ATTRIB | SIG = ASSIGN | input SIG | outputSIG
SIG ::= [STR:0] FIELD | STR FIELD
FIELD ::= P SUFFIX | Q SUFFIX
SUFFIX ::= val | ack | transid | transid unique | active | stable | data
TNAME, P, Q ::= STR

YOU MUST LEARN THE RULES ABOVE, THEN ANALYZE the RTL module interface and implementation and WRITE AUTOSVA annotations.
DO NOT answer anything except for the annotations.
*/