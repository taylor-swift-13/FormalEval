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
   Keys: "first_name" (lower), "Last_Name" (mixed), "city" (lower), "Income" (mixed), "FIRST_NAME" (upper) *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name" \/ k = "city".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Last_Name", "Doe"); ("city", "new yorAgek"); ("Income", "$50,000"); ("FIRST_NAME", "Jane")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. discriminate H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all_lower is true. We show contradiction using "Last_Name". *)
      (* "Last_Name" is the 2nd element. *)
      inversion H_lower; subst. (* 1st element: "first_name" *)
      inversion H2; subst. (* 2nd element: "Last_Name" *)
      destruct H3 as [_ H_bad].
      unfold is_lower_test in H_bad.
      (* "Last_Name" must be "first_name" or "city" *)
      destruct H_bad as [H_eq | H_eq]; discriminate H_eq.
      
    + (* Case: all_upper is true. We show contradiction using "first_name". *)
      (* "first_name" is the 1st element. *)
      inversion H_upper; subst. (* 1st element: "first_name" *)
      destruct H1 as [_ H_bad].
      unfold is_upper_test in H_bad.
      (* "first_name" must be "FIRST_NAME" *)
      discriminate H_bad.
Qed.