%{
  open Dag 
%}
%token <int> NAT
%token <string> ID
%token UNIT
%token COMMA
%token RPAREN LPAREN EOF
%token COLON 
%token BAR
%token ARROW

%type <Dag.graph> graph

%start graph
%%
let graph := ID;~=node*;EOF;<>
let node := 
  | id = NAT; COLON; head = ID; args = param_list; ARROW; body = int_list; {{id; head; args; body}} 
  | id = NAT; COLON; head = ID; ARROW; body = int_list; {{id; head; args=[]; body}}
  | id = NAT; COLON; head = ID; args = param_list; {{id; head; args; body=[]}}

let param_list :=
  | ~ = delimited(LPAREN, int_list, RPAREN); <>
  | UNIT; { [] }
let int_list :=
  | ~ = separated_nonempty_list(COMMA, integer); <>
let integer := 
    | BAR ;i = NAT ; {-i}
    | ~=NAT ; <>
