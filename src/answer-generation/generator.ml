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
      gen_max_steps : int option;
      gen_max_results : int option;
    }
  ;;

  type generation_parameters = {
    gen_reference : generator_reference;
    gen_evaluation : Interpreter.evaluation;
    gen_target_vars : Ast.ident list;
  }
  ;;

  type generation_result = {
    gen_answers : Answer.t list;
    gen_num_answers : int;
    gen_is_complete : bool;
  }

  val create :
    ?exploration_policy:Interpreter.exploration_policy ->
    ?max_steps:(int option) ->
    ?max_results:(int option) ->
    configuration -> expr -> ident list ->
    generation_parameters
  ;;

  val generate_answers :
    ?generation_callback:(Answer.t -> unit) ->
    generation_parameters ->
    generation_result
end;;

module Make(Answer : Answer) = struct
  module Answer = Answer;;

  type generator_reference = {
    gen_program : expr;
    gen_cfg : Ddpa_graph.ddpa_graph;
    gen_exploration_policy : Interpreter.exploration_policy;
    gen_max_steps : int option;
    gen_max_results : int option;
  }
  ;;

  type generation_parameters = {
    gen_reference : generator_reference;
    gen_evaluation : Interpreter.evaluation;
    gen_target_vars : Ast.ident list;
  }
  ;;

  type generation_result = {
    gen_answers : Answer.t list;
    gen_num_answers : int;
    gen_is_complete : bool;
  }
  ;;

  let update_target_vars
      (results : Interpreter.evaluation_result list)
      (x_list : Ident.t list)
    : Ident.t * Ident.t list =
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
      lazy_logger `trace (fun () ->
        "Remaining filtered target vars: " ^
        "[" ^ (String.join "; " @@ List.map Ident.show x_list_filtered) ^ "]"
      );
      (* let _ =
        print_endline @@
        "Remaining filtered target vars: " ^
        "[" ^ (String.join "; " @@ List.map Ident.show x_list_filtered) ^ "]"
      in *)
      (x, x_list_filtered)
  ;;

  let rec take_steps
      ?generation_callback:(generation_callback=fun _ -> ())
      (gen_ref : generator_reference)
      (prev_complete : bool)
      (answers : Answer.t list)
      (steps : int)
      (x_list : Ident.t list)
      (ev : Interpreter.evaluation)
    : generation_result =
    let recurse = take_steps ~generation_callback gen_ref in
    match gen_ref.gen_max_results, gen_ref.gen_max_steps with
    | (Some max_res, _) when List.length answers >= max_res ->
      begin
        lazy_logger `trace (fun () ->
          "Pass reached max number of results; terminating generation.");
        {
          gen_answers = answers;
          gen_num_answers = List.length answers;
          gen_is_complete = false;
        }
      end
    | (_, Some max_steps) when steps >= max_steps ->
      begin
        match x_list with
        | [] | _ :: [] ->
          lazy_logger `trace (fun () ->
            "Pass reached max step count; terminating generation.");
          {
            gen_answers = answers;
            gen_num_answers = List.length answers;
            gen_is_complete = false;
          }
        | _ :: x' :: x_list' ->
          lazy_logger `trace (fun () ->
            "Pass reached max step count with remaining target vars; restart generation.");
          let ev' =
            Interpreter.start
              ~exploration_policy:gen_ref.gen_exploration_policy
              gen_ref.gen_cfg
              gen_ref.gen_program
              x'
          in
          recurse false answers 0 (x' :: x_list') ev'
      end
    | _, _ ->
      begin
        let results, ev'_opt = Interpreter.step ev in
        let (x, x_list') = update_target_vars results x_list in
        let answers' =
          results
          |> List.map (Answer.answer_from_result steps gen_ref.gen_program x)
          |> List.filter (Answer.generation_successful)
        in
        let steps' = steps + 1 in
        begin
          match answers' with
          | [] ->
            lazy_logger `trace (fun () -> "No answer found on iteration.");
          | _ :: _ ->
            List.iter
              (fun ans ->
                lazy_logger `trace (fun () -> "Found answer on iteration.");
                (* TODO: Remove debug print *)
                (* let _ = print_endline "Found answer on iteration!!!\n" in *)
                generation_callback ans)
              answers'
        end;
        let answers'' = answers' @ answers in
        match ev'_opt with
        | Some ev' ->
          lazy_logger `trace (fun () ->
            "Continue current evaluation.");
          recurse prev_complete answers'' steps' (x :: x_list') ev'
        | None ->
          (* Start a new evaluation if there's start vars left in the list. *)
          match x_list' with
          | [] ->
            lazy_logger `trace (fun () ->
              "Evaluation complete and no more variables left; stop.");
            {
              gen_answers = answers'';
              gen_num_answers = List.length answers'';
              gen_is_complete = prev_complete;
            }
          | (x' :: _) ->
            lazy_logger `trace (fun () ->
              "Evaluation complete with target variables left; restart evaluation.");
            let ev' =
              Interpreter.start
                ~exploration_policy:gen_ref.gen_exploration_policy
                gen_ref.gen_cfg
                gen_ref.gen_program
                x'
            in
            recurse prev_complete answers'' 0 x_list' ev'
    end
  ;;

  let generate_answers
      ?generation_callback:(generation_callback=(fun _ -> ()))
      (gen_params : generation_parameters)
    : generation_result =
    take_steps
      ~generation_callback
      gen_params.gen_reference
      true
      []
      0
      gen_params.gen_target_vars
      gen_params.gen_evaluation
  ;;

  let create
      ?exploration_policy:(exploration_policy=Interpreter.Explore_breadth_first)
      ?max_steps:(max_steps=None)
      ?max_results:(max_results=None)
      (conf : configuration)
      (e : expr)
      (x_list : ident list)
    : generation_parameters =
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
        gen_max_steps = max_steps;
        gen_max_results = max_results
      }
    in
    { 
      gen_reference = gen_reference;
      gen_target_vars = x_list;
      gen_evaluation = evaluation;
    }
  ;;

end;;