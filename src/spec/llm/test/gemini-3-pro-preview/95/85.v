Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Section CheckDictCase.

  (* Abstract types to represent Python's dynamic typing *)
  Variable Key : Type.
  Variable Value : Type.

  (* Predicates corresponding to Python's type checking and string methods *)
  Variable is_str : Key -> Prop.
  Variable is_lower : Key -> Prop.
  Variable is_upper : Key -> Prop.

  Definition check_dict_case_spec (dict : list (Key * Value)) (res : bool) : Prop :=
    let keys := map fst dict in
    match keys with
    | [] => res = false
    | _ => 
        let all_lower := Forall (fun k => is_str k /\ is_lower k) keys in
        let all_upper := Forall (fun k => is_str k /\ is_upper k) keys in
        res = true <-> (all_lower \/ all_upper)
    end.

End CheckDictCase.

(* Concrete definitions for the test case *)
Definition key_impl := string.
Definition val_impl := string.

(* Predicates for the specific test case: 
   Only 'first_name' and 'city' are lower. 
   Only 'FIRST_NAME' is upper. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name" \/ k = "city".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Last_Name", "Dooe"); ("Age", "35"); ("city", "New York"); 
     ("Income", "$50,000"); ("FIRST_NAME", "Anew"); ("1", "36"); ("Incyellowome", "INCOMEJohn"); 
     ("chINCEOMEerryAge", "$50,00"); ("Last_Namme", "fruit")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. discriminate H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all keys are lower *)
      (* We show contradiction because "Last_Name" is in the list (2nd element) but not lower *)
      inversion H_lower; subst. (* first_name *)
      inversion H2; subst. (* Last_Name *)
      destruct H3 as [_ H_is_lower].
      unfold is_lower_test in H_is_lower.
      destruct H_is_lower as [H_eq | H_eq]; discriminate H_eq.
      
    + (* Case: all keys are upper *)
      (* We show contradiction because "first_name" is in the list (1st element) but not upper *)
      inversion H_upper; subst. (* first_name *)
      destruct H1 as [_ H_is_upper].
      unfold is_upper_test in H_is_upper.
      discriminate H_is_upper.
Qed.