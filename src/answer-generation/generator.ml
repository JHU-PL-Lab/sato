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

  type generator =
    {
      gen_program : expr;
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

module Make(Answer : Answer) : Generator = struct
  module Answer = Answer;;

  type generator =
    {
      gen_program : expr;
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
      (e : expr)
      (x : Ident.t)
      (max_steps : int)
      (evaluation : Interpreter.evaluation)
    : generation_result =
    let rec take_one_step
        (step_count : int)
        (ev : Interpreter.evaluation)
      : generation_result =
      lazy_logger `trace (fun () -> Printf.sprintf
                          "%d/%d completed in this pass" step_count max_steps);
      if step_count = max_steps then begin
        lazy_logger `trace (fun () ->
            "Pass reached max step count; returning suspended generator.");
        { gen_answers = [];
          gen_steps = step_count;
          gen_generator =
            { gen_program = e;
              gen_target = [x];
              generator_fn = Some(fun n -> take_steps e x n ev)
            };
        }
      end else begin
        let results, ev'_opt = Interpreter.step ev in
        if List.is_empty results then begin
          lazy_logger `trace (fun () -> "No new results found in this step.");
          match ev'_opt with
          | Some ev' ->
            (* No result and no termination.  Keep running. *)
            lazy_logger `trace (fun () ->
                "Interpreter evaluation not yet complete; continuing.");
            take_one_step (step_count + 1) ev'
          | None ->
            (* No result and no remaining computation; we terminated!  Give
              back a result indicating as much. *)
            lazy_logger `trace (fun () ->
                "Interpreter evaluation complete; stopping.");
            { gen_answers = [];
              gen_steps = step_count + 1;
              gen_generator =
                { gen_program = e;
                  gen_target = [x];
                  generator_fn = None;
                };
            }
        end else begin
          (* We have results! *)
          lazy_logger `trace (fun () -> "New result found in this step.");
          let answers = List.map (Answer.answer_from_result e x) results in
          let generator_fn =
            match ev'_opt with
            | None -> None
            | Some ev' -> Some(fun n -> take_steps e x n ev')
          in
          { gen_answers = answers;
            gen_steps = step_count + 1;
            gen_generator =
              { gen_program = e;
                gen_target = [x];
                generator_fn = generator_fn;
              };
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
    let target_vars =
      Interpreter_environment.list_instrument_conditionals e
    in
    let _ = target_vars in
    let x = List.hd x_list in
    let evaluation =
      Interpreter.start
      ~exploration_policy:exploration_policy
      cfg e x
    in
    { gen_program = e;
      gen_target = x_list;
      generator_fn = Some(fun n -> take_steps e x n evaluation)
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
    _log_trace_start_generating original_generator.gen_program;
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