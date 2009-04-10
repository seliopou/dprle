%{
(*  Copyright (c) 2008-2009, University of Virginia
    All rights reserved.
   
    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:
       * Redistributions of source code must retain the above copyright
         notice, this list of conditions and the following disclaimer.
       * Redistributions in binary form must reproduce the above
         copyright notice, this list of conditions and the following
         disclaimer in the documentation and/or other materials
         provided with the distribution.
       * Neither the name of the University of Virginia  nor the names 
         of its contributors may be used to endorse or promote products
         derived from this software without specific prior written
         permission.
   
    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
    (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
    STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
    ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
    OF THE POSSIBILITY OF SUCH DAMAGE.
   
    Author: Pieter Hooimeijer
*)
  open Lexing
  open Depgraph
  open Interface

  type nfa = Nfa.nfa
  
  let tempcount = ref 0

  let new_temp () = 
    incr tempcount ;
    "_t" ^ string_of_int(!tempcount)

  let parse_error s =
    flush stdout

  let curnfa : (nfa option) ref = ref None
  let cur_int = ref 0
  let name_mapping = Hashtbl.create 500

  let to_int_state (q : string) : int =
    try Hashtbl.find name_mapping q with
	Not_found ->
	  Hashtbl.replace name_mapping q !cur_int;
	  incr cur_int;
	  !cur_int - 1
    
  let reset_int_state () : unit =
    cur_int := 0;
    Hashtbl.clear name_mapping

  let output_error b e message = 
    let startpos = Parsing.rhs_start_pos b in
    let endpos  = Parsing.rhs_end_pos e in
      Printf.printf "\n# Error (%d.%d-%d.%d): %s\n"
	startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
	endpos.pos_lnum   (endpos.pos_cnum - endpos.pos_bol)
	message;
      curnfa := None;
      reset_int_state ();
      raise Options.Known_error

  let wrong_state b e =
    output_error b e "Use select(n) to choose an assignment first"

  let cur_graph = Interface.cur_graph
%}

%token LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN COMMA ARROW QUOTE SUBSET 
%token SEMICOLON PUSH POP SOLVE SOLVEALL RESET ON ANY DOT EPSILON START FINAL 
%token DELTA UNKNOWN ALIAS NEG CHARACTERSTART QSUBSET QEQUAL
%token <string> IDENT SYMBOL INDEX
%token <int> SELECT
%token <string list> MACHINES
%token <int * (string list)> STRINGS

%start statement
%type <unit> statement

%%
statement:  expr SUBSET error 
             { output_error 3 3 "Expected identifier or machine definition" }
           | expr SUBSET rhs error 
	     { output_error 4 4 "Expected ';'" }
           | expr SUBSET rhs SEMICOLON
             { let varname, is_nfa = $3 in
		 try 
		   intersect varname $1
		 with WrongState -> wrong_state 1 4
	     }
	   | IDENT QSUBSET IDENT SEMICOLON
	       { (try issubset $1 $3 with
		    | WrongState -> wrong_state 1 4
		    | BadIdent v -> output_error 1 4 ("Identifier '" ^ v ^ "' is unbound"))
               }
	   | IDENT QEQUAL IDENT SEMICOLON
               { (try areequal $1 $3 with
		    | WrongState -> wrong_state 1 4
		    | BadIdent v -> output_error 1 4 ("Identifier '" ^ v ^ "' is unbound"))
	       }
	   | IDENT ALIAS IDENT DOT IDENT SEMICOLON {
	       (try named_concat $3 $5 $1 
		with CantAlias -> 
		  output_error 1 4 ("Node " ^ $1 ^ " already represents a concatenation")
		  | WrongState -> wrong_state 1 4)
	     }
	   | command error 
	     { output_error 2 2 "Expected ';'" }

           | command SEMICOLON 
	     { match $1 with 
		 | PUSH -> push()
		 | POP  -> (try pop () with Pop -> 
			      output_error 1 2 "Too many calls to pop()")
		 | SOLVE ->
		     (try solve ((Parsing.rhs_start_pos 1).pos_lnum) false
		      with WrongState -> wrong_state 1 2)
		 | SOLVEALL ->
		     (try solve ((Parsing.rhs_start_pos 1).pos_lnum) true
		      with WrongState -> wrong_state 1 2)
		 | RESET ->
		     reset_all ();
		 | SELECT n ->
		     (try 
			select n
		      with WrongState -> output_error 1 2 "Only the current solution is available"
			| BadSelectIndex -> output_error 1 2 "Index out of range")
		 | MACHINES idl ->
		     (try
			show_machines idl
		      with WrongState -> wrong_state 1 2
			| BadIdent v -> output_error 1 2 ("Identifier '" ^ v ^ "' is unbound"))
		 | STRINGS (number, identlist) ->
		     (try 
			gen_strings identlist
		      with WrongState -> wrong_state 1 2
			| BadIdent v -> output_error 1 2 ("Identifier '" ^ v ^ "' is unbound"))
		 | _ -> failwith "Not possible."
	     }

rhs:       IDENT { ($1, false) }
           | machinedef
	     { let varname = new_temp () in 
		 ignore (try new_node varname (Machine $1)
		  with WrongState -> wrong_state 1 1);
		 (varname, true)
	     }
	   | NEG error {
	       output_error 2 2 "Expected NFA definition"
	     }
	   | NEG machinedef 
	     { let varname = new_temp () in
	       let machine = (Nfa.nfa_to_dfa $2) in
		 Nfa.complement machine;
		 ignore (try (new_node varname (Machine machine)) with
		    WrongState -> wrong_state 1 2);
		 (varname, true)
	      }

expr:    concatlist { $1 }

concatlist : IDENT { $1 }
	   | concatlist error 
             { output_error 2 2 "Expected '.' or 'subset'" }
	   | concatlist DOT error
	     { output_error 3 3 "Expected identifier" }
	   | concatlist DOT IDENT 
	     { let varname = new_temp () in
		 anon_concat $1 $3 varname; 
		 varname
             }
	     
machinedef: LBRACKET error 
	     { output_error 2 2 "Expected 's:'" }
	   | LBRACKET START error 
	     { output_error 3 3 "Expected identifier" }
	   | LBRACKET START IDENT error
             { output_error 4 4 "Expected 'f:'" }
	   | LBRACKET START IDENT FINAL error 
	     { output_error 5 5 "Expected identifier" }
	   | LBRACKET START IDENT FINAL IDENT error 
	     { output_error 6 6 "Expected 'd:'" }
	   | LBRACKET START IDENT FINAL IDENT DELTA transitionlist RBRACKET
	     { let newnfa = match !curnfa with 
                 | None -> 
		     Nfa.new_nfa_states (to_int_state $3) (to_int_state $5)
                 | Some nfa -> 
		     nfa.Nfa.s <- (to_int_state $3);
		     nfa.Nfa.f <- (to_int_state $5); nfa
	       in
		 curnfa := None; 
		 reset_int_state ();
		 newnfa
	     }

transitionlist: /* empty */ { }
           | transitionlist transition { }

transition: error 
             { output_error 1 1 ("Expected ']' or transition of the form " ^
		 "'IDENT -> IDENT on { SYMBOLS }'")
	     } 
	   | IDENT error 
	     { output_error 2 2 "Expected '->'" }
	   | IDENT ARROW error 
	     { output_error 3 3 "Expected identifier" }
	   | IDENT ARROW IDENT error 
	     { output_error 4 4 "Expected 'on'" }
	   | IDENT ARROW IDENT ON error
	     { output_error 5 5 
		 "Expected {}-delimited set of characters, 'epsilon', 'any', or 'neg'" 
             }
           | IDENT ARROW IDENT ON ANY
	     { let nfa = match !curnfa with 
		 | None ->
		     let newnfa = Nfa.new_nfa_states 0 1 in
		       curnfa := (Some newnfa); 
		       newnfa
		 | Some nfa -> nfa
	       in
		 Nfa.add_all_trans nfa (to_int_state $1) (to_int_state $3)
	     }
	   | IDENT ARROW IDENT ON EPSILON
	     { let nfa = match !curnfa with 
		 | None ->
		     let newnfa = Nfa.new_nfa_states 0 1 in
		       curnfa := (Some newnfa); 
		       newnfa
		 | Some nfa -> nfa
	       in
		 Nfa.add_trans nfa (to_int_state $1) Nfa.Epsilon (to_int_state $3)
	     }
           | IDENT ARROW IDENT ON symbolset
	     { let nfa = match !curnfa with 
		 | None ->
		     let newnfa = Nfa.new_nfa_states 0 1 in
		       curnfa := (Some newnfa);
		       newnfa
		 | Some nfa -> nfa
	       in
		 List.iter (fun x -> Nfa.add_trans nfa (to_int_state $1) 
			                               (Nfa.Character x) (to_int_state $3)) $5
	     }
	   | IDENT ARROW IDENT ON NEG symbolset
	     { let nfa = match !curnfa with 
		 | None ->
		     let newnfa = Nfa.new_nfa_states 0 1 in
		       curnfa := (Some newnfa);
		       newnfa
		 | Some nfa -> nfa
	       in
	       let symbols = Charset.from_list $6 in
	       let symbols = Charset.minus (Charset.create_full ()) symbols in
		 Charset.iter (fun x -> Nfa.add_trans nfa (to_int_state $1) 
				 (Nfa.Character x) (to_int_state $3)) symbols
	     }

symbolset: LBRACE RBRACE 
	    { [] }
          | LBRACE symbollist RBRACE 
	    { $2  }
          | LBRACE symbollist COMMA RBRACE 
	    { $2 }

symbollist: symbol 
            { [ $1 ] }
	  | symbollist COMMA symbol
            { $3 :: $1 }

symbol: error 
	    { output_error 1 1 ("Unrecognized symbol; expecting a single-quote" ^
                                " delimited symbol or a decimal character code")
	    }
          | SYMBOL 
	    { 
	      try Charset.string_to_int $1 with Charset.IllegalChar -> 
		output_error 1 1 "Unrecognized symbol; expected a single character"
            }
	  | CHARACTERSTART INDEX
	    { try Charset.digit_list_to_int $2 with Charset.IllegalChar ->
                output_error 1 2 ("Unrecognized symbol; expected a decimal character" ^
                                  " code of the form \nnn")
            }

command:  IDENT LPAREN paramoption RPAREN
	    { output_error 1 1 "Unrecognized command" }
          | PUSH LPAREN RPAREN
	    { PUSH }
	  | POP  LPAREN RPAREN
	    { POP } 
          | SOLVE LPAREN RPAREN
	    { SOLVE }
	  | SOLVEALL LPAREN RPAREN
	    { SOLVEALL }
	  | RESET LPAREN RPAREN
	    { RESET }
	  | SELECT LPAREN INDEX RPAREN
              {      
		let index = 
		try int_of_string $3 with _ -> 
		  output_error 1 4 "Select takes an integer argument" in
		SELECT index
	      }
	  | MACHINES LPAREN identlist RPAREN { MACHINES $3 }
	  | STRINGS LPAREN identlist RPAREN { STRINGS (1, $3) }
	  | STRINGS LPAREN INDEX COMMA identlist RPAREN { 
	      let index = try int_of_string $3 with _ ->
		output_error 3 3 "Invalid number of strings specified" 
	      in
		if index <= 0 then 
		  output_error 3 3 "Invalid number of strings specified" ;
		STRINGS (index, $5) 
            }

identlist: { [] }
	  | nonemptyidentlist { $1 }

nonemptyidentlist:
	  | IDENT { [$1]} 
          | identlist COMMA IDENT { $1 @ [$3] }

paramoption : /* empty */ { }
	    | INDEX {}
            | identlist{ }
	    | error { }
