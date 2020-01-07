open Eldarica
open Dag

let _ =
   let g = parse_file "tmp" in
   List.iter (
     fun x -> Printf.printf "%s" x.head;
     List.iter (fun y -> Printf.printf "%d" y) x.args
   ) g
