open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

let log_src = Logs.Src.create "Refine"
module Log = (val Logs.src_log log_src)

let with_logs_disabled f =
  let level = Logs.Src.level log_src in
  Logs.Src.set_level log_src None;
  let r = f () in
  Logs.Src.set_level log_src level;
  r
module TraceVar = TraceVar
module HornClause = HornClause

type guard = HornClause.body
let empty_guard : guard = { pvs = []; phi = [] }

(* [(tv, (e, guard)) \in reduce_env] means that
 * `when [tv] was bound to [e], [guard] holded`.
 * *)
type reduce_env = (TraceExpr.t * guard) TraceVar.Map.t
