(**
   This module gives an implementation of the DDPA analysis.  It is parametric
   in the choice of context stack.
*)

open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast;;
open Ddpa_abstract_ast;;
open Ddpa_analysis_logging;;
open Ddpa_context_stack;;
open Ddpa_graph;;
open Ddpa_utils;;
open Nondeterminism;;
open Pp_utils;;

let logger = Logger_utils.make_logger "Ddpa_analysis";;
let lazy_logger = Logger_utils.make_lazy_logger "Ddpa_analysis";;

module type Analysis_sig =
sig
  (** The type of the DDPA analysis generated by the module. *)
  type ddpa_analysis

  (** The context stack module for this analysis. *)
  module C : Context_stack;;

  (** The initial, unclosed analysis derived from an expression. *)
  val create_initial_analysis :
    ?ddpa_logging_config:(ddpa_analysis_logging_config option) ->
    expr -> ddpa_analysis

  (** Pretty-prints a DDPA structure. *)
  val pp_ddpa_analysis : ddpa_analysis pretty_printer
  val show_ddpa_analysis : ddpa_analysis -> string

  (** Get size of DDPA and underlying PDS. *)
  val get_size : ddpa_analysis -> int * int * int * int * int

  (** Performs a series of closure steps on an analysis.  This is not guaranteed
      to complete closure; however, it will make progress as long as the
      argument is not fully closed. *)
  val perform_closure_steps : ddpa_analysis -> ddpa_analysis

  (** Determines if an analysis is fully closed. *)
  val is_fully_closed : ddpa_analysis -> bool

  (** Fully closes an analysis. *)
  val perform_full_closure : ddpa_analysis -> ddpa_analysis

  (** Determines the values at a given position of the provided variable in the
      given analysis.  This is an approximation -- false positives may arise --
      but it is guaranteed to be conservative if the analysis is fully closed.
      The returned analysis contains a cache structure to accelerate answering
      of this question in the future. *)
  val values_of_variable :
    abstract_var -> annotated_clause -> ddpa_analysis ->
    Abs_value_set.t * ddpa_analysis

  val contextual_values_of_variable :
    abstract_var -> annotated_clause -> C.t -> ddpa_analysis ->
    Abs_value_set.t * ddpa_analysis

  (** Retrieves from an analysis the CFG it has constructed. *)
  val cfg_of_analysis : ddpa_analysis -> ddpa_graph
end;;

(**
   A functor which constructs a DDPA analysis module.
*)
module Make(C : Context_stack)
  : Analysis_sig with module C = C =
struct
  module C = C;;
  module Structure_types = Ddpa_pds_structure_types.Make(C);;
  module Dynamic_pop_types =
    Ddpa_pds_dynamic_pop_types.Make(C)(Structure_types)
  ;;
  module Dynamic_pop_handler =
    Ddpa_pds_dynamic_pop_handler.Make(C)(Structure_types)(Dynamic_pop_types)
  ;;

  module Ddpa_pds_reachability_basis =
  struct
    module State = Structure_types.Pds_state;;
    module Stack_element = Structure_types.Pds_continuation;;
  end

  module Ddpa_pds_reachability =
    Pds_reachability.Make
      (Ddpa_pds_reachability_basis)
      (Dynamic_pop_handler)
      (Pds_reachability_work_collection_templates.Work_stack)
  ;;

  open Ddpa_pds_reachability.Stack_action.T;;
  open Ddpa_pds_reachability.Terminus.T;;

  module Edge_functions =
    Ddpa_pds_edge_functions.Make
      (C)
      (Structure_types)
      (Dynamic_pop_types)
      (Ddpa_pds_reachability_basis)
      (Ddpa_pds_reachability)
  ;;

  type ddpa_analysis_logging_data =
    { ddpa_logging_config : ddpa_analysis_logging_config
    ; ddpa_closure_steps : int
    }
  [@@deriving show]
  ;;
  let _ = show_ddpa_analysis_logging_data;;

  type ddpa_analysis =
    { ddpa_graph : ddpa_graph
    ; ddpa_graph_fully_closed : bool
    ; pds_reachability : Ddpa_pds_reachability.analysis
    ; ddpa_active_nodes : Annotated_clause_set.t
    (** The active nodes in the DDPA graph.  This set is maintained
            incrementally as edges are added. *)
    ; ddpa_active_non_immediate_nodes : Annotated_clause_set.t
    (** A subset of [ddpa_active_nodes] which only contains the
        non-immediate nodes.  This is useful during closure. *)
    ; ddpa_logging_data : ddpa_analysis_logging_data option
    (** Data associated with logging, if appropriate. *)
    ; ddpa_end_of_block_map : End_of_block_map.t
    (** A dictionary mapping each clause to its end-of-block clause. *)
    }
  [@@deriving show]
  ;;

  let dump_yojson analysis =
    `Assoc
      [ ( "ddpa_graph"
        , Ddpa_graph.to_yojson analysis.ddpa_graph
        )
      ; ( "ddpa_graph_fully_closed"
        , `Bool analysis.ddpa_graph_fully_closed
        )
      ; ( "ddpa_active_nodes"
        , Annotated_clause_set.to_yojson analysis.ddpa_active_nodes
        )
      ; ("ddpa_active_non_immediate_nodes"
        , Annotated_clause_set.to_yojson
            analysis.ddpa_active_non_immediate_nodes
        )
      ]
  ;;

  (** Logs a given PDS reachability graph.  This only occurs if the logging
      level of the analysis is at least as high as the one provided in this
      call.  The graph to be logged defaults to the analysis but can be
      overridden (e.g. in the logger given to that analysis). *)
  let log_pdr level ddpa_logging_data_opt reachability =
    match ddpa_logging_data_opt with
    | None -> ()
    | Some data ->
      if compare_ddpa_logging_level
          data.ddpa_logging_config.ddpa_pdr_logging_level
          level >= 0
      then
        begin
          let json =
            `Assoc
              [ ( "element_type"
                , `String "pds_reachability_graph"
                )
              ; ( "work_count"
                , `Int (Ddpa_pds_reachability.get_work_count reachability)
                )
              ; ( "graph"
                , Ddpa_pds_reachability.dump_yojson reachability
                )
              ]
          in
          data.ddpa_logging_config.ddpa_json_logger json
        end
  ;;

  (** As log_pdr, but logs a delta of the reachability graph. *)
  let log_pdr_delta
      level ddpa_logging_data_opt old_reachability new_reachability =
    match ddpa_logging_data_opt with
    | None -> ()
    | Some data ->
      if compare_ddpa_logging_level
          data.ddpa_logging_config.ddpa_pdr_logging_level
          level >= 0
      then
        begin
          let json =
            `Assoc
              [ ( "element_type"
                , `String "pds_reachability_graph_delta"
                )
              ; ( "work_count"
                , `Int (Ddpa_pds_reachability.get_work_count new_reachability)
                )
              ; ( "graph"
                , Ddpa_pds_reachability.dump_yojson_delta
                    old_reachability new_reachability
                )
              ]
          in
          data.ddpa_logging_config.ddpa_json_logger json
        end
  ;;

  (** Logs a given DDPA control flow graph.  This only occurs if the logging
      level of the analysis is at least as high as the one provided in this
      call. *)
  let log_cfg level analysis =
    match analysis.ddpa_logging_data with
    | None -> ()
    | Some data ->
      if compare_ddpa_logging_level
          data.ddpa_logging_config.ddpa_cfg_logging_level
          level >= 0
      then
        begin
          let json =
            `Assoc
              [ ( "element_type"
                , `String "ddpa_graph"
                )
              ; ( "work_count"
                , `Int (Ddpa_pds_reachability.get_work_count
                          analysis.pds_reachability)
                )
              ; ( "graph"
                , dump_yojson analysis
                )
              ]
          in
          data.ddpa_logging_config.ddpa_json_logger json
        end
  ;;

  let get_size analysis =
    let pds_node_count, pds_edge_count =
      Ddpa_pds_reachability.get_size analysis.pds_reachability
    in
    let filter_inferrable_nodes nodes =
      nodes
      |> Annotated_clause_set.filter (
        fun node ->
          match node with
          | Binding_enter_clause _
          | Binding_exit_clause _
          | Nonbinding_enter_clause _ -> false
          | _ -> true
      )
    in
    Annotated_clause_set.cardinal (filter_inferrable_nodes analysis.ddpa_active_nodes),
    Annotated_clause_set.cardinal (filter_inferrable_nodes analysis.ddpa_active_non_immediate_nodes),
    analysis.ddpa_graph
    |> edges_of
    |> List.of_enum
    |> List.length,
    pds_node_count,
    pds_edge_count
  ;;

  (**
     Adds a set of edges to the DDPA graph.  This implicitly adds the vertices
     involved in those edges.  Note that this does not affect the end-of-block
     map.
  *)
  let add_edges edges_in analysis =
    let edges =
      edges_in
      |> Enum.filter
        (fun edge -> not @@ Ddpa_graph.has_edge edge analysis.ddpa_graph)
    in
    if Enum.is_empty edges then (analysis,false) else
      (* ***
         First, update the PDS reachability analysis with the new edge
         information.
      *)
      let add_edge_for_reachability edge reachability =
        reachability
        |> Ddpa_pds_reachability.add_edge_function
          (Edge_functions.create_edge_function edge)
        |> Ddpa_pds_reachability.add_untargeted_dynamic_pop_action_function
          (Edge_functions.create_untargeted_dynamic_pop_action_function
             analysis.ddpa_end_of_block_map edge)
      in
      let pds_reachability' =
        Enum.clone edges
        |> Enum.fold (flip add_edge_for_reachability) analysis.pds_reachability
      in
      (* ***
         Next, add the edge to the DDPA graph.
      *)
      let ddpa_graph' =
        Enum.clone edges
        |> Enum.fold (flip Ddpa_graph.add_edge) analysis.ddpa_graph
      in
      (* ***
         Now, perform closure over the active node set.  This function uses a
         list of enumerations of nodes to explore.  This reduces the cost of
         managing the work queue.
      *)
      let rec find_new_active_nodes from_acls_enums results_so_far =
        match from_acls_enums with
        | [] -> results_so_far
        | from_acls_enum::from_acls_enums' ->
          if Enum.is_empty from_acls_enum
          then find_new_active_nodes from_acls_enums' results_so_far
          else
            let from_acl = Enum.get_exn from_acls_enum in
            if Annotated_clause_set.mem from_acl analysis.ddpa_active_nodes ||
               Annotated_clause_set.mem from_acl results_so_far
            then find_new_active_nodes from_acls_enums results_so_far
            else
              let results_so_far' =
                Annotated_clause_set.add from_acl results_so_far
              in
              let from_here = ddpa_graph' |> Ddpa_graph.succs from_acl in
              find_new_active_nodes (from_here::from_acls_enums) results_so_far'
      in
      let (ddpa_active_nodes',ddpa_active_non_immediate_nodes') =
        let new_active_root_nodes =
          Enum.clone edges
          |> Enum.filter_map
            (fun (Ddpa_edge(acl_left,acl_right)) ->
               if Annotated_clause_set.mem acl_left analysis.ddpa_active_nodes
               then Some acl_right
               else None)
          |> Enum.filter
            (fun acl ->
               not @@ Annotated_clause_set.mem acl analysis.ddpa_active_nodes)
        in
        let new_active_nodes =
          find_new_active_nodes [new_active_root_nodes]
            Annotated_clause_set.empty
        in
        ( Annotated_clause_set.union analysis.ddpa_active_nodes
            new_active_nodes
        , Annotated_clause_set.union analysis.ddpa_active_non_immediate_nodes
            ( new_active_nodes |> Annotated_clause_set.filter
                (not % is_annotated_clause_immediate) )
        )
      in
      (
        { ddpa_graph = ddpa_graph'
        ; ddpa_graph_fully_closed = false
        ; pds_reachability =  pds_reachability'
        ; ddpa_active_nodes = ddpa_active_nodes'
        ; ddpa_active_non_immediate_nodes = ddpa_active_non_immediate_nodes'
        ; ddpa_logging_data = analysis.ddpa_logging_data
        ; ddpa_end_of_block_map = analysis.ddpa_end_of_block_map
        }
      , true
      )
  ;;

  let create_initial_analysis
      ?ddpa_logging_config:(ddpa_logging_config_opt=None)
      e =
    (* Begin by constructing a logging structure. *)
    let logging_data_opt =
      match ddpa_logging_config_opt with
      | None -> None
      | Some config ->
        Some { ddpa_logging_config = config
             ; ddpa_closure_steps = 0 (* FIXME: this number never changes or gets reported! *)
             }
    in
    (* Lift the expression. *)
    let Abs_expr(cls) = lift_expr e in
    (* Put the annotated clauses together. *)
    let rx = rv cls in
    let acls =
      List.enum cls
      |> Enum.map (fun x -> Unannotated_clause x)
      |> Enum.append (Enum.singleton (Start_clause rx))
      |> flip Enum.append (Enum.singleton (End_clause rx))
    in
    (* For each pair, produce a DDPA edge. *)
    let rec mk_edges acls' =
      match Enum.get acls' with
      | None -> []
      | Some acl1 ->
        match Enum.peek acls' with
        | None -> []
        | Some acl2 ->
          Ddpa_edge(acl1,acl2) :: mk_edges acls'
    in
    let edges = List.enum @@ mk_edges acls in
    (* Construct an empty analysis. *)
    let pdr_log_fn_opt =
      match logging_data_opt with
      | None -> None
      | Some logging_data ->
        if logging_data.ddpa_logging_config.ddpa_pdr_logging_level
           = Log_nothing
        then None
        else Some
            (fun old_reachability new_reachability ->
               if logging_data.ddpa_logging_config.ddpa_pdr_deltas
               then
                 log_pdr_delta Log_everything logging_data_opt
                   old_reachability new_reachability
               else
                 log_pdr Log_everything logging_data_opt new_reachability)
    in
    (* The initial reachability analysis should include an edge function which
       always allows discarding the bottom-of-stack marker. *)
    let initial_reachability =
      Ddpa_pds_reachability.empty ~logging_function:pdr_log_fn_opt ()
      |> Ddpa_pds_reachability.add_edge_function
        (fun state ->
           Enum.singleton ([Pop Structure_types.Bottom_of_stack],
                           Static_terminus state)
        )
    in
    let empty_analysis =
      { ddpa_graph = Ddpa_graph.empty
      ; ddpa_graph_fully_closed = true
      ; pds_reachability = initial_reachability
      ; ddpa_active_nodes =
          Annotated_clause_set.singleton (Start_clause rx)
      ; ddpa_active_non_immediate_nodes = Annotated_clause_set.empty
      ; ddpa_logging_data = logging_data_opt
      ; ddpa_end_of_block_map = create_end_of_block_map cls
      }
    in
    (* Put the edges into the empty analysis. *)
    let analysis = fst @@ add_edges edges empty_analysis in
    logger `trace "Created initial analysis";
    log_cfg Log_everything analysis;
    log_pdr Log_everything analysis.ddpa_logging_data analysis.pds_reachability;
    analysis
  ;;

  let restricted_values_of_variable x acl ctx analysis =
    Logger_utils.lazy_bracket_log (lazy_logger `trace)
      (fun () ->
         Printf.sprintf "Determining values of variable %s at position %s"
           (show_abstract_var x) (show_annotated_clause acl)
      )
      (fun (values, _) ->
         let pp formatter values =
           pp_concat_sep_delim "{" "}" ", " pp_abstract_value formatter @@
           Enum.clone values
         in
         pp_to_string pp values
      )
    @@ fun () ->
    let open Structure_types in
    let start_state = Program_point_state(acl,ctx) in
    let start_actions =
      [Push Bottom_of_stack; Push (Lookup_var(x))]
    in
    let reachability = analysis.pds_reachability in
    let reachability' =
      reachability
      |> Ddpa_pds_reachability.add_start_state start_state start_actions
      |> Ddpa_pds_reachability.fully_close
    in
    let analysis' = { analysis with pds_reachability = reachability' } in
    let values =
      reachability'
      |> Ddpa_pds_reachability.get_reachable_states start_state start_actions
      |> Enum.filter_map
        (function
          | Program_point_state _ -> None
          | Result_state v -> Some v)
    in
    (values, analysis')
  ;;

  let values_of_variable x acl analysis =
    let (values, analysis') =
      restricted_values_of_variable x acl C.empty analysis
    in
    (Abs_value_set.of_enum values, analysis')
  ;;

  let contextual_values_of_variable x acl ctx analysis =
    let (values, analysis') =
      restricted_values_of_variable x acl ctx analysis
    in
    (Abs_value_set.of_enum values, analysis')
  ;;

  let perform_closure_steps analysis =
    begin
      match analysis.ddpa_logging_data with
      | None -> lazy_logger `trace (fun () -> "Performing closure step")
      | Some data -> lazy_logger `trace (fun () ->
          (Printf.sprintf "Performing closure step %d"
             (data.ddpa_closure_steps+1)));
    end;
    (* We need to do work on each of the active, non-immediate nodes.  This
       process includes variable lookups, which may result in additional work
       being done; as a result, each closure step might change the underlying
       graph.  We'll keep the analysis in a ref so that, whenever work is done
       which produces a new analysis, we can just update the ref. *)
    let analysis_ref = ref analysis in
    let new_edges_enum = Nondeterminism_monad.enum
        (
          let open Nondeterminism_monad in
          let%bind acl =
            pick_enum @@
            Annotated_clause_set.enum analysis.ddpa_active_non_immediate_nodes
          in
          let has_values x pred =
            let (values,analysis') =
              restricted_values_of_variable x acl C.empty !analysis_ref
            in
            analysis_ref := analysis';
            Enum.exists pred values
          in
          match acl with
          | Unannotated_clause(Abs_clause(x1,Abs_appl_body(x2,x3)) as cl) ->
            lazy_logger `trace
              (fun () ->
                 Printf.sprintf "Considering application closure for clause %s"
                   (show_abstract_clause cl));
            (* Make sure that a value shows up to the argument. *)
            [%guard has_values x3 (fun _ -> true)];
            (* Get each of the function values. *)
            let (x2_values,analysis_2) =
              restricted_values_of_variable x2 acl C.empty !analysis_ref
            in
            analysis_ref := analysis_2;
            let%bind x2_value = pick_enum x2_values in
            let%orzero Abs_value_function(fn) = x2_value in
            (* Wire each one in. *)
            return @@ wire_function cl fn x3 x1 analysis_2.ddpa_graph
          | Unannotated_clause(
              Abs_clause(x1,Abs_conditional_body(x2,e1,e2)) as cl) ->
            lazy_logger `trace
              (fun () ->
                 Printf.sprintf "Considering conditional closure for clause %s"
                   (show_abstract_clause cl));
            (* We have two functions we may wish to wire: f1 (if x2 has values
               which match the pattern) and f2 (if x2 has values which antimatch
               the pattern). *)
            [ (true, e1);
              (false, e2);
            ]
            |> List.enum
            |> Enum.filter_map
              (fun (then_branch, body_expr) ->
                 let pred = function
                   | Abs_value_bool n -> n = then_branch
                   | _ -> false
                 in
                 if has_values x2 pred then
                   Some (body_expr, then_branch)
                 else
                   None
              )
            |> Enum.map (fun (Abs_expr(body), then_branch) ->
                wire_conditional
                  cl then_branch body x1 (!analysis_ref).ddpa_graph
              )
            |> Nondeterminism_monad.pick_enum
          | _ ->
            raise @@ Utils.Invariant_failure
              "Unhandled clause in perform_closure_steps"
        )
                         |> Enum.concat
    in
    (* Due to the stateful effects of computing the new edges, we're going to
       want to pull on the entire enumeration before we start looking at the
       analysis. *)
    let new_edges_list = List.of_enum new_edges_enum in
    (* Now we want to add all of the new edges.  If there are any new ones, we
       need to know about it. *)
    let (analysis',any_new) =
      add_edges (List.enum new_edges_list) !analysis_ref
    in
    let ddpa_logging_data' =
      match analysis'.ddpa_logging_data with
      | None -> None
      | Some data ->
        Some { data with ddpa_closure_steps = data.ddpa_closure_steps+1 }
    in
    let result =
      { analysis' with
        ddpa_graph_fully_closed = not any_new;
        ddpa_logging_data = ddpa_logging_data'
      }
    in
    begin
      match result.ddpa_logging_data with
      | None -> logger `trace "Completed closure step"
      | Some data -> lazy_logger `trace
                       (fun () -> Printf.sprintf "Completed closure step %d"
                           (data.ddpa_closure_steps));
    end;
    log_cfg Log_everything result;
    result
  ;;

  let is_fully_closed analysis = analysis.ddpa_graph_fully_closed;;

  let rec perform_full_closure analysis =
    if is_fully_closed analysis
    then
      begin
        logger `trace "Closure complete.";
        log_pdr Log_result analysis.ddpa_logging_data analysis.pds_reachability;
        log_cfg Log_result analysis;
        analysis
      end
    else
      begin
        perform_full_closure @@ perform_closure_steps analysis
      end
  ;;

  let cfg_of_analysis analysis =
    analysis.ddpa_graph
  ;;
end;;
