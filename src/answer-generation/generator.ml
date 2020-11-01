open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Ast_pp;;

open Generator_answer;;
open Generator_configuration;;

module Interpreter =
  Odefa_symbolic_interpreter.Interpreter;;
module Interpreter_environment =
  Odefa_symbolic_interpreter.Interpreter_environment;;
module Interpreter_types =
  Odefa_symbolic_interpreter.Interpreter_types;;
module Relative_stack =
  Odefa_symbolic_interpreter.Relative_stack;;
module Solver =
  Odefa_symbolic_interpreter.Solver;;

let lazy_logger = Logger_utils.make_lazy_logger "Generator";;

module type Generator = sig
  module Answer : Answer;;

  type generator_reference =
    {      
      gen_program : expr;
      gen_cfg : Ddpa_graph.ddpa_graph;
      gen_exploration_policy : Interpreter.exploration_policy;
    }
  ;;

  type generator =
    {
      generator_reference : generator_reference;
      gen_target : Ident.t list;
      generator_fn : (int -> generation_result) option
    }

  and generation_result =
    {
      gen_answers : Answer.t list;
      gen_steps : int;
      gen_generator : generator;
    }
  ;;

  val create :
    ?exploration_policy:Interpreter.exploration_policy ->
    configuration -> expr -> ident list -> generator
  ;;

  val generate_answers :
    ?generation_callback:(Answer.t -> int -> unit) ->
    int option -> generator ->
    (Answer.t list * int) list * generator option
  ;;
end;;

module Make(Answer : Answer) = struct
  module Answer = Answer;;

  type generator_reference =
    {
      gen_program : expr;
      gen_cfg : Ddpa_graph.ddpa_graph;
      gen_exploration_policy : Interpreter.exploration_policy;
    }
  ;;

  type generator =
    {
      generator_reference : generator_reference;
      gen_target : Ident.t list;
      generator_fn : (int -> generation_result) option
    }

  and generation_result =
    {
      gen_answers : Answer.t list;
      gen_steps : int;
      gen_generator : generator;
    }
  ;;

  let rec take_steps
      (gen_ref : generator_reference)
      (x_list : Ident.t list)
      (max_steps : int)
      (evaluation : Interpreter.evaluation)
    : generation_result =
    let rec take_one_step
        (step_count : int)
        (ev : Interpreter.evaluation)
      : generation_result =
      lazy_logger `trace (fun () ->
        Printf.sprintf "%d/%d completed in this pass" step_count max_steps);
      (* Suspend computation if we reached the max number of steps *)
      if step_count = max_steps then begin
        lazy_logger `trace (fun () ->
          "Pass reached max step count; returning suspended generator.");
        { gen_answers = [];
          gen_steps = step_count;
          gen_generator =
            { generator_reference = gen_ref;
              gen_target = x_list;
              generator_fn = Some(fun n -> take_steps gen_ref x_list n ev)
            };
        }
      end else begin
        let results, ev'_opt = Interpreter.step ev in
        let (x, x_list') =
          match x_list with
          | [] ->
            raise @@ Invalid_argument "cannot have empty list of start vars"
          | x :: x_list_tl ->
            (* Eliminate already-visited vars from the list *)
            let visited =
              List.fold_left
                (fun accum res ->
                  Ident_set.union accum res.Interpreter.er_visited
                )
                Ident_set.empty
                results
            in
            let x_list_filtered =
              List.filter
                (fun cls_id ->
                  match Ident_set.Exceptionless.find cls_id visited with
                  | None -> true
                  | Some _ -> false
                )
              x_list_tl
            in
            (x, x_list_filtered)
        in
        let steps = step_count + 1 in
        let answers =
          List.map
            (Answer.answer_from_result steps gen_ref.gen_program x)
            results
        in
        match answers, ev'_opt with
        | [], Some ev' ->
          (* No result and no termination.  Keep running the same loop. *)
          lazy_logger `trace (fun () ->
            "Interpreter evaluation not yet complete. Continuing.");
          take_one_step steps ev'
        | _, Some ev' ->
          lazy_logger `trace (fun () ->
            "New result found in this step. Continuing evaluation.");
          { gen_answers = answers;
            gen_steps = steps;
            gen_generator =
              { generator_reference = gen_ref;
                gen_target = x_list;
                generator_fn = Some(fun n -> take_steps gen_ref x_list n ev');
              };
          }
        | _, None ->
          (* Start a new evaluation if there's start vars left in the list. *)
          if not @@ List.is_empty answers then begin
            lazy_logger `trace (fun () ->
              "New result found in this step. Current evaluation terminated.")
          end;
          begin
            let gen_fn_opt =
              match x_list' with
              | [] ->
                lazy_logger `trace (fun () ->
                  "No additional targets. Interpreter evaluation complete.");
                None
              | (x' :: _) ->
                lazy_logger `trace (fun () ->
                  Format.sprintf
                    "Start new evaluation at new variable %s." (show_ident x'));
                let ev' =
                  Interpreter.start
                    ~exploration_policy:gen_ref.gen_exploration_policy
                    gen_ref.gen_cfg
                    gen_ref.gen_program
                    x'
                in
                Some(fun n -> take_steps gen_ref x_list' n ev')
            in
            {
              gen_answers = answers;
              gen_steps = steps;
              gen_generator = {
                generator_reference = gen_ref;
                gen_target = x_list';
                generator_fn = gen_fn_opt;
              }
            }
          end
      end
    in
    take_one_step 0 evaluation
  ;;

  let create
      ?exploration_policy:(exploration_policy=Interpreter.Explore_breadth_first)
      (conf : configuration)
      (e : expr)
      (x_list : ident list)
    : generator =
    let module Stack = (val conf.conf_context_model) in
    let module Analysis = Ddpa_analysis.Make(Stack) in
    let cfg =
      e
      |> Analysis.create_initial_analysis
      |> Analysis.perform_full_closure
      |> Analysis.cfg_of_analysis
    in
    let x = List.hd x_list in
    lazy_logger `trace
      (fun () -> Format.sprintf "Starting evaluation at variable %s" (show_ident x));
    let evaluation = Interpreter.start ~exploration_policy cfg e x in
    let gen_reference =
      {
        gen_program = e;
        gen_cfg = cfg;
        gen_exploration_policy = exploration_policy;
      }
    in
    {
      generator_reference = gen_reference;
      gen_target = x_list;
      generator_fn = Some(fun n -> take_steps gen_reference x_list n evaluation)
    }
  ;;

  (* Logging functions *)

  let _log_trace_start_generating expr =
    lazy_logger `trace
      (fun () -> "Generating answers for expression:\n" ^
              Pp_utils.pp_to_string pp_expr expr)
  ;;

  let _log_trace_exhausted_steps () =
    lazy_logger `trace
      (fun () -> "Out of generation steps; stopping with waiting generator.")
  ;;

  let _log_trace_non_exhausted_steps steps_to_take =
    lazy_logger `trace
    (fun () -> Printf.sprintf
        "Taking up to %d step%s of generation in this loop" steps_to_take
        (if steps_to_take = 1 then "" else "s"));
  ;;

  let _log_trace_generation_terminated () =
    lazy_logger `trace
      (fun () -> "Generation terminated with no further results.");
  ;;

  let _log_trace_took_steps steps_so_far steps_taken =
    lazy_logger `trace
      (fun () -> Printf.sprintf "Took %d step%s (%d so far)"
          steps_so_far
          (if steps_so_far = 1 then "" else "s")
          steps_taken);
  ;;

  let generate_answers
      ?generation_callback:(generation_callback=fun _ _ -> ())
      (max_steps_opt : int option)
      (original_generator : generator)
    : (Answer.t list * int) list * generator option =
    _log_trace_start_generating original_generator.generator_reference.gen_program;
    let max_steps_per_loop = 100 in
    (* Keep running the generator until we run out of steps per loop *)
    let rec loop
        (gen : generator)
        (steps_left_opt : int option)
        (steps_taken : int)
        (results : (Answer.t list * int) list)
      : (Answer.t list * int) list * generator option =
      let steps_to_take =
        match steps_left_opt with
        | None -> max_steps_per_loop
        | Some n -> min n max_steps_per_loop
      in
      if steps_to_take = 0 then begin
        (* We ran out of steps, so we are quitting now! *)
        _log_trace_exhausted_steps ();
        (results, Some gen)
      end else begin
        _log_trace_non_exhausted_steps steps_to_take;
        match gen.generator_fn with
        | None ->
          (* No further generation is possible. *)
          _log_trace_generation_terminated ();
          (results, None)
        | Some fn ->
          (* Further generation is possible, so run it *)
          let result = fn steps_to_take in
          let steps_taken' = steps_taken + result.gen_steps in
          _log_trace_took_steps result.gen_steps steps_taken';
          begin
            (* Run the callback for any discovered answers *)
            match result.gen_answers with
            | _ :: _ ->
              List.iter
                (fun answer ->
                  lazy_logger `trace (fun () -> "Found answer on iteration.");
                  generation_callback answer steps_taken')
                result.gen_answers
            | [] ->
              lazy_logger `trace (fun () -> "No answer found on iteration.");
          end;
          let results' = (result.gen_answers, steps_taken') :: results in
          let steps_left_opt' =
            Option.map (fun n -> max 0 @@ n - result.gen_steps) steps_left_opt
          in
          loop result.gen_generator steps_left_opt' steps_taken' results'
      end
    in
    loop original_generator max_steps_opt 0 []
  ;;
end;;