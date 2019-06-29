
%{
open Hflmc2_util
open Raw_hflz
%}

%token <int> INT
%token <string> LIDENT
%token <string> UIDENT

%token START_HES EOF
%token LPAREN  "(" RPAREN  ")"
%token LSQUARE "[" RSQUARE "]"
%token LANGRE  "<" RANGRE  ">"
%token TRUE FALSE
%token LAMBDA DOT "."
%token DEF_G "=v"
%token DEF_L "=m"

%token PLUS  "+" MINUS "-" STAR  "*" NEG
%token EQ "=" NEQ "<>" LE "<=" GE ">=" /* LT "<" GT ">" */
%token AND "&&" OR "||"

%right OR
%right AND
%left PLUS MINUS
%left STAR
%nonassoc NEG

%type <Raw_hflz.hes> hes
%start hes

%%

hes:
| START_HES hflz_rule+ EOF { $2 }

hflz_rule:
| uvar lvar* def_fixpoint hflz DOT
    { { var  = $1
      ; args = $2
      ; fix  = $3
      ; body = $4
      }
    }

hflz:
| abs_expr { $1 }

abs_expr:
| lambda* and_or_expr { mk_abss $1 $2 }

and_or_expr:
| and_or_expr "&&" and_or_expr { mk_ands [$1;$3] }
| and_or_expr "||" and_or_expr { mk_ors  [$1;$3] }
| modal_expr                   { $1 }

modal_expr:
| "[" LIDENT "]" pred_expr { mk_forall $2 $4 }
| "<" LIDENT ">" pred_expr { mk_exists $2 $4 }
| pred_expr                { $1 }

pred_expr:
| arith_expr                 { $1               }
| arith_expr pred arith_expr { mk_pred $2 $1 $3 }

arith_expr:
| app_expr                 { $1                }
| arith_expr op arith_expr { mk_op $2  [$1;$3] }
| "-" arith_expr %prec NEG { mk_op Arith.Sub [mk_int 0;$2] }

app_expr:
| atom atom* { mk_apps $1 $2 }

atom:
| INT  { mk_int   $1 }
| bool { mk_bool  $1 }
| lvar { mk_var   $1 }
| uvar { mk_var   $1 }
| "(" hflz ")" { $2 }

%inline op:
| "+" { Arith.Add  }
| "-" { Arith.Sub  }
| "*" { Arith.Mult }

pred:
| "="  { Formula.Eq  }
| "<>" { Formula.Neq }
| "<=" { Formula.Le  }
| ">=" { Formula.Ge  }
| "<"  { Formula.Lt  }
| ">"  { Formula.Gt  }

def_fixpoint:
| "=v" { Fixpoint.Greatest }
| "=m" { Fixpoint.Least    }

lambda:
| LAMBDA lvar "." { $2 }

lvar:
| LIDENT { $1 }

uvar:
| UIDENT { $1 }

bool:
| TRUE  { true  }
| FALSE { false }

