open Enumerators;;
open Alschemes;;
open PropFormula;;
open Basics;;
open Satwrapper;;
open Output;;


let timeout = ref 15.0
		  
class virtual checkEngine =
  object (self)
    val mutable continue = true
                         
    method virtual step: unit
                 
    method run = while continue && !timeout > 0.0 do
		   let f = Sys.time () in
		   self#step;
		   timeout := !timeout -. (Sys.time () -. f)
		 done
  end

        
class simpleSatEngine props params constrs sphi defs report outProg =
  object (self)
    inherit checkEngine

    val mutable first = true
    val mutable counter = 0
    val enumerator = makeEnumerator params

(*
    method private collect_propositions =
      let rec collect = function Biimp(f,g)    -> PropSet.union (collect f) (collect g)
                               | And fs        -> List.fold_left (fun s -> fun f -> PropSet.union s (collect f)) PropSet.empty fs
                               | Or fs         -> List.fold_left (fun s -> fun f -> PropSet.union s (collect f)) PropSet.empty fs
                               | Lit(b,x,a,ps) -> PropSet.singleton (x,ps)
                               | _             -> PropSet.empty
      in
      collect  
 *)
                   
    method step = output 1 0 ("\nRunning iteration " ^ string_of_int counter ^ "\n");
                  output 1 1 "Constructing parameter evaluation ............ ";
                  let eval = match enumerator#get counter with
                      None        -> continue <- false;
                                     ParamEval.empty
                    | Some result -> make_eval result
                  in
                  output 1 0 (showEval eval ^ "\n");
                  if continue || first then
                    begin
                      let constraints_sat = try
	                  List.fold_left (fun b -> fun (x,f,y) -> b && (match ((ParamEval.find x eval), (ParamEval.find y eval)) with
							                  (Int x', Int y') -> f x' y'
		            (* | _                -> failwith "Constraints can only name parameters of type NAT!" *) ))
		            true constrs
	                with Not_found -> failwith "Constraints can only refer to formal parameters!"
	              in
                   
	              (if constraints_sat then
	                 begin
                           output 1 1 "Instantiation yields formula ................. ";
	                   let phi = instantiate sphi defs eval in
                           output 1 0 (showFormula phi ^ "\n");
                           
                           output 1 1 "Tidying yields ............................... ";
                           let phi' = tidy phi in
                           output 1 0 (showFormula phi' ^ "\n");
                           
                           output 1 1 "Collecting propositions ...................... ";
                           let props' = PropSet.elements (collect_propositions phi') in
                           output 1 0 (String.concat ", " (List.map (fun (x,ps) -> showFormula (Lit(true,x,ps))) props') ^ "\n");
                           
                           output 1 1 "Transformation to CNF yields ................. ";
                           let phi'' = toCNF phi' in
                           output 1 0 (showCNF phi'' ^ "\n");

                           output 1 1 "Getting new solver ........................... ";
                           let solver = new Satwrapper.satWrapper (Satsolvers.get_default ()) in
                           output 1 0 "done.\n";

                           (try
                             output 1 1 "Adding clauses ............................... ";
                             List.iter (fun cls -> solver#add_clause_list (List.map (function Lit(b,x,ps) -> if b then Po(x,ps) else Ne(x,ps)
                                                                                            | _           -> failwith ("checkEngine.run: detected unexpected non-literal while processing CNF!"))
                                                                             cls))
                               phi'';
                             output 1 0 "done.\n";
                             
                             output 1 1 "Solving ...................................... ";
                             solver#solve;
                           
                             (match solver#get_solve_result with
                                SolveSatisfiable   -> output 1 0 "satisfiable!\n";
                                                      output 1 1 "Collecting relevant literals from solution ... ";
                                                      let lits = List.map (fun (x,ps) -> let b = solver#get_variable_bool (x,ps) in
                                                                                         Lit(b,x,ps))
                                                                   (List.filter (fun (x,_) -> StringSet.mem x props) props')
                                                      in
                                                      output 1 0 "done.\n";
                                                      output 1 0 (report eval true lits ^ "\n")
                              | SolveUnsatisfiable -> output 1 0 "unsatisfiable!\n";
                                                      output 1 0 (report eval false [] ^ "\n")
                              | SolveFailure s     -> failwith s);
                           with Minisat.Unsat -> begin
                                                   output 1 0 "unsatisfiable!\n";
                                                   output 1 0 (report eval false [] ^ "\n")
                                                 end);

                           run_output_language params solver outProg;

                           solver#dispose
	                 end
                       else
                         output 1 0 "discarded.\n");
                      
                      first <- false;
                      counter <- counter + 1
                    end
                  else
                    begin
                      output 1 0 "stopped.\n"
                    end
  end                                            

class modelsEngine props params constrs sphi defs initreport eachreport outProg =
  object (self)
    inherit checkEngine

    val mutable counter = 0
    val mutable models = 0
    val mutable satisfiable = true
    val mutable first = true
    val enumerator = makeEnumerator params
                            
    method step = satisfiable <- true;
                  models <- 0;
                  output 1 0 ("\nRunning iteration " ^ string_of_int counter ^ "\n");
                  output 1 1 "Constructing parameter evaluation ............ ";
                  let eval = match enumerator#get counter with
                      None        -> continue <- false;
                                     ParamEval.empty
                    | Some result -> make_eval result
                  in
                  output 1 0 (showEval eval ^ "\n");
                  if continue || first then
                    begin
                      let constraints_sat = try
	                  List.fold_left (fun b -> fun (x,f,y) -> b && (match ((ParamEval.find x eval), (ParamEval.find y eval)) with
							                  (Int x', Int y') -> f x' y'
		            (* | _                -> failwith "Constraints can only name parameters of type NAT!" *) ))
		            true constrs
	                with Not_found -> failwith "Constraints can only refer to formal parameters!"
	              in
                   
	              (if constraints_sat then
	                 begin
                           output 1 1 "Instantiation yields formula ................. ";
	                   let phi = instantiate sphi defs eval in
                           output 1 0 (showFormula phi ^ "\n");
                           
                           output 1 1 "Tidying yields ............................... ";
                           let phi' = tidy phi in
                           output 1 0 (showFormula phi' ^ "\n");
                           
                           output 1 1 "Collecting propositions ...................... ";
                           let props' = PropSet.elements (collect_propositions phi') in
                           output 1 0 (String.concat ", " (List.map (fun (x,ps) -> showFormula (Lit(true,x,ps))) props') ^ "\n");
                           
                           output 1 1 "Transformation to CNF yields: ";
                           let phi'' = toCNF phi' in
                           output 1 0 (showCNF phi'' ^ "\n");
                           
                           output 1 1 "Getting new solver ........................... ";
                           let solver = new Satwrapper.satWrapper (Satsolvers.get_default ()) in
                           output 1 0 "done.\n";
                           
                           output 1 1 "Adding clauses ............................... ";
                           List.iter (fun cls -> solver#add_clause_list (List.map (function Lit(b,x,ps) -> if b then Po(x,ps) else Ne(x,ps)
                                                                                          | _             -> failwith ("checkEngine.run: detected unexpected non-literal while processing CNF!"))
                                                                           cls))
                             phi'';
                           output 1 0 "done.\n";
                           
                           output 1 0 (initreport eval ^ "\n");
                           
                           while satisfiable do
                             output 1 1 "Solving ...................................... ";
                             solver#solve;
                             output 1 0 "done.\n";
                             
                             (match solver#get_solve_result with
                                SolveUnsatisfiable -> satisfiable <- false 
                              | SolveFailure s     -> failwith s
                              | _                  -> ());
                             
                             (if satisfiable then
                                begin
                                  output 1 0 "satisfiable!\n";
                                  output 1 1 "Collecting relevant literals from solution ... ";
                                  let solution = List.map (fun (x,ps) -> let b = solver#get_variable_bool (x,ps) in
                                                                         Lit(b,x,ps))
                                                   (List.filter (fun (x,_) -> StringSet.mem x props) props')
                                  in
                                  let dual_clause = List.map (function Lit(b,x,ps) -> if b then Ne(x,ps) else Po(x,ps) | _ -> failwith "checkEngine.run: detected non-literal") solution
                                  in
                                  output 1 0 (eachreport true solution models ^ "\n");
                                  models <- models + 1;
                                  output 1 1 "Adding new clause ............................ ";
				  solver#incremental_reset;
                                  solver#add_clause_list dual_clause;
                                  output 1 1 "done.\n"
                                end
                              else
                                begin
                                  output 1 0 "unsatisfiable!\n";
                                  output 1 0 (eachreport false [] models ^ "\n")
                                end)
                           done;

                           run_output_language params solver outProg;

                           solver#dispose
	                 end
                       else
                         output 1 0 "discarded.\n");
                      
                      first <- false;
                      counter <- counter + 1
                    end
                  else
                    output 1 0 "stopped.\n"

  end

class simplePi2Engine props params constrs sphi spsi defs report = 
  object (self)
    inherit checkEngine

    val mutable counter = 0
    val mutable has_models_phi = true
    val mutable has_no_model_psi = false
    val mutable first = true
    val enumerator = makeEnumerator params
                            
    method step = has_models_phi <- true;
                  has_no_model_psi <- false;
                  output 1 0 ("\nRunning iteration " ^ string_of_int counter ^ "\n");
                  output 1 1 "Constructing parameter evaluation ............ ";
                  let eval = match enumerator#get counter with
                      None        -> continue <- false;
                                     ParamEval.empty
                    | Some result -> make_eval result
                  in
                  output 1 0 (showEval eval ^ "\n");
                  if continue || first then
                    begin
                      let constraints_sat = try
	                  List.fold_left (fun b -> fun (x,f,y) -> b && (match ((ParamEval.find x eval), (ParamEval.find y eval)) with
							                  (Int x', Int y') -> f x' y'
		            (* | _                -> failwith "Constraints can only name parameters of type NAT!" *) ))
		            true constrs
	                with Not_found -> failwith "Constraints can only refer to formal parameters!"
	              in
                   
	              (if constraints_sat then
	                 begin
			   output 1 1 "Setting up first formula .....................\n";
			   
	                   output 1 1 "Instantiation yields formula ................. ";
                           let phi = instantiate sphi defs eval in
                           output 1 0 (showFormula phi ^ "\n");
                           
                           output 1 1 "Occurring propositions ....................... ";
                           let props' = collect_propositions phi in
                           output 1 0 (String.concat ", " (List.map (fun (x,ps) -> showFormula (Lit(true,x,ps))) (PropSet.elements props')) ^ "\n");

			   output 1 1 "Relevant for model comparison ................ ";
			   let props'' = PropSet.filter (fun (x,_) -> StringSet.mem x props) props' in
			   output 1 0 (String.concat ", " (List.map (fun (x,ps) -> showFormula (Lit(true,x,ps))) (PropSet.elements props'')) ^ "\n");

                           output 1 1 "Tidying yields ............................... ";
                           let phi' = tidy phi in
                           output 1 0 (showFormula phi' ^ "\n");
                           
                           output 1 1 "Transformation to CNF yields ................. ";
                           let phi'' = toCNF phi' in
                           output 1 0 (showCNF phi'' ^ "\n");
                           
                           output 1 1 "Getting new solver #1 ........................ ";
                           let solver_phi = new Satwrapper.satWrapper (Satsolvers.get_default ()) in
                           output 1 0 "done.\n";
                           
			   output 1 1 "Setting up second formula ....................\n";
			   
                           output 1 1 "Instantiation yields formula ................. ";
	                   let psi = instantiate spsi defs eval in
                           output 1 0 (showFormula psi ^ "\n");
                           
                           output 1 1 "Tidying yields ............................... ";
                           let psi' = tidy psi in
                           output 1 0 (showFormula psi' ^ "\n");
                           
                           output 1 1 "Transformation to CNF yields ................. ";
                           let psi'' = toCNF psi' in
                           output 1 0 (showCNF psi'' ^ "\n");

                           output 1 1 "Getting new solver #2 ........................ ";
                           let solver_psi = new Satwrapper.satWrapper (Satsolvers.get_default ()) in
                           output 1 0 "done.\n";

                           output 1 1 "Adding clauses of 1st formula ................ ";
                           List.iter (fun cls -> solver_phi#add_clause_list (List.map (function Lit(b,x,ps) -> if b then Po(x,ps) else Ne(x,ps)
                                                                                              | _             -> failwith ("checkEngine.run: detected unexpected non-literal while processing CNF!"))
                                                                               cls))
                             phi'';
                           output 1 0 "done.\n";

                           output 1 1 "Adding clauses of 2nd formula ................ ";
                           List.iter (fun cls -> solver_psi#add_clause_list (List.map (function Lit(b,x,ps) -> if b then Po(x,ps) else Ne(x,ps)
                                                                                              | _             -> failwith ("checkEngine.run: detected unexpected non-literal while processing CNF!"))
                                                                               cls))
                             psi'';
                           output 1 0 "done.\n";

                           while has_models_phi && not has_no_model_psi do
                               output 1 1 "Solving 1st formula .......................... ";
                               solver_phi#solve;
                           
                               (match solver_phi#get_solve_result with
                                  SolveUnsatisfiable -> has_models_phi <- false 
                                | SolveFailure s     -> failwith s
                                | _                  -> ());

                               if has_models_phi then
                                  begin
                                    output 1 0 "satisfiable!\n";
                                    output 1 1 "Collecting relevant literals from solution ... ";
                                    let solution = List.map (fun (x,ps) -> let b = solver_phi#get_variable_bool (x,ps) in
                                                                           Lit(b,x,ps))
                                                             (PropSet.elements props'')
                                    in
                                    output 1 0 (String.concat "," (List.map showFormula solution) ^ "\n");
                                    
                                    output 1 1 "Solving 2nd formula with assumptions ......... ";
                                    let assumptions = List.map (function Lit(b,x,ps) -> if b then Po(x,ps) else Ne(x,ps)
                                                                       | _           -> failwith ("checkEngine.run:detected unexpected non-literal while construction assumption list!"))
                                                        solution
                                    in
                                    solver_psi#solve_with_assumptions assumptions;
                           
                                    (match solver_psi#get_solve_result with
                                       SolveUnsatisfiable -> has_no_model_psi <- true 
                                     | SolveFailure s     -> failwith s
                                     | _                  -> ());

                                    if not has_no_model_psi then
                                      begin
                                        output 1 0 "satisfiable!\n";
                                        output 1 1 "Adding new clause to 1st formula ............. ";
                                        let dual_clause = List.map (function Lit(b,x,ps) -> if b then Ne(x,ps) else Po(x,ps) | _ -> failwith "checkEngine.run: detected non-literal") solution
                                        in
				        solver_phi#incremental_reset;
                                        solver_psi#incremental_reset;
                                        solver_phi#add_clause_list dual_clause;
                                        output 1 0 "done.\n"
                                      end
                                    else
                                      begin
                                        output 1 0 "unsatisfiable!\n";
                                        output 0 0 (report false eval solution ^ "\n")
                                      end
                                  end
                               else
                                 output 1 0 "unsatisfiable!\n";  
                           done;
                           output 1 1 "Disposing solvers ............................ ";
                           solver_phi#dispose;
                           solver_psi#dispose;
                           output 1 0 "done\n";
                           if not has_no_model_psi then output 0 0 (report true eval [] ^ "\n")
                         end
                       else
                         output 1 0 "discarded.\n");
                      
                      first <- false;
                      counter <- counter + 1
                    end
                  else
                    output 1 0 "stopped.\n"
  end
  
class combinedEngine (es: checkEngine array) =
object (self)
  inherit checkEngine
  val mutable i = 0

  method private increase = i <- i+1;
                            if i >= Array.length es then i <- 0
                            
  method step = (es.(i))#step; self#increase 
end
  
