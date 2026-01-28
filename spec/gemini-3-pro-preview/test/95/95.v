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
   'first_name' and 'city' are lower. 
   'FIRST_NAME' and '_FIRST_NAME' are upper. 
   Others are mixed or neither strictly lower nor upper for all chars. *)
Definition is_str_test (k : key_impl) : Prop := True.

Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "city".

Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME" \/ k = "_FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); 
     ("Last_Name", "Doe"); 
     ("city", "new yorAgek"); 
     ("Income", "$50,000"); 
     ("FIRST_NAME", "Jane"); 
     ("_FIRST_NAME", "JNew YorNke"); 
     ("new yorAgeIncIomekIncome", "1")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    
    + (* Case: All keys are lower *)
      (* We need to show a contradiction because "FIRST_NAME" is in the list but not lower *)
      (* "FIRST_NAME" is the 5th element in the list *)
      inversion H_lower; subst. (* 1st: first_name *)
      inversion H2; subst.      (* 2nd: Last_Name *)
      inversion H4; subst.      (* 3rd: city *)
      inversion H6; subst.      (* 4th: Income *)
      inversion H8; subst.      (* 5th: FIRST_NAME *)
      
      (* H9 contains the property for "FIRST_NAME" *)
      destruct H9 as [_ H_is_lower].
      unfold is_lower_test in H_is_lower.
      (* H_is_lower states "FIRST_NAME" is "first_name" or "city", which is false *)
      destruct H_is_lower; discriminate.
      
    + (* Case: All keys are upper *)
      (* We need to show a contradiction because "first_name" is in the list but not upper *)
      (* "first_name" is the 1st element in the list *)
      inversion H_upper; subst. (* 1st: first_name *)
      
      (* H1 contains the property for "first_name" *)
      destruct H1 as [_ H_is_upper].
      unfold is_upper_test in H_is_upper.
      (* H_is_upper states "first_name" is "FIRST_NAME" or "_FIRST_NAME", which is false *)
      destruct H_is_upper; discriminate.
Qed.