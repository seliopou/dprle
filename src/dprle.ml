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
       * Neither the name of the University of Virginia nor the names 
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

open Interface

let header   = "# Decision Procedure for Regular Language Equations" ^        
  "\n# Copyright (c) 2008-2009, University of Virginia"
 let revision = "$Revision: 258 $"

let printerror s =
  Printf.printf "# Error: %s\n" s;
  flush stdout

(* Parse and execute the contents provided by lexbuf *)
let process (lexbuf : Lexing.lexbuf) =
  try
    while true do
      Parse.statement Lex.handletop lexbuf;
      flush stdout;
    done
  with End_of_file -> ()

let process_file (s : string) = 
  let _ = if !Options.reset then reset_all () in
    try 
      let channel = open_in s in
	(try
	   let lexbuf = Lexing.from_channel channel in
	     Printf.printf "# Processing file %s\n" s;
	     flush stdout;
	     process lexbuf;
	     close_in_noerr channel
	 with Options.Known_error ->
	   (* Stop execution if abort-on-errors was specified *)
	   close_in_noerr channel;
	   if not (!Options.noerr) then exit(-1))
    with Sys_error _ ->
      printerror ("Failed to open " ^ s);
      if not (!Options.noerr) then exit(-1)

let process_stdin () =
  Printf.printf "# Processing from stdin\n";
  flush stdout;
  reset_all ();
  let lexbuf = Lexing.from_channel stdin in
    try
      while true do 
	try flush stdout; Parse.statement Lex.handletop lexbuf
	with Options.Known_error -> ()
	  | Parsing.Parse_error -> Printf.printf "# Error: Uncaught parse error, ignoring most recent statement\n"
      done
    with End_of_file -> ()

(* MAIN *)
let main () = 
  let argspec = [ ("-debug", Arg.Set Options.debug,
		   " Enable debugging output");
                  ("-show-min-dfa", Arg.Set Options.minimize,
                   " Print NFAs as minimal DFAs during output");  
                  ("-cleanup-nfas", Arg.Set Options.elim,
                   " Remove dead states from NFAs");  
		  ("-no-context-reset", Arg.Clear Options.reset,
		   " Do not reset the environment for each input file");
		  ("-abort-on-error", Arg.Clear Options.noerr,
		   " Do not continue with next input file on error");
		  ("-nfa-cap-size n", Arg.Set_int Options.maxsize,
		   " Minimize NFA intersect operand if it has more than n states")
		] in
  let argspec = Arg.align argspec in
  let files = ref [] in
  let addinputfile x = files := x::!files in
    Arg.parse argspec addinputfile "Usage: dprle [options] [input files]";
    Printf.printf "%s\n# %s\n" header revision;
    Options.print_options ();
    files := List.rev !files;
    
    match !files with
      | f::fs -> (if not !Options.reset then reset_all (); 
		  List.iter process_file !files)
      | _ -> process_stdin ();;

main() ;;

