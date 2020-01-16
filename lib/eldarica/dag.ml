(*
 * node_id : head(args) -> body
 * *)

type node = {id: int; head: string; args: int list; body: int list}
type graph = node list

let debug = List.iter (
  fun x -> 
  Printf.printf "%s" x.head;
  List.iter (fun y -> Printf.printf " %d" y) x.args;
  print_newline ()
)