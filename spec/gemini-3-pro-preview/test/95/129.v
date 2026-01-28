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
   Only 'first_name' and 'city' are lowercase.
   Only 'FIRST_NAME' is uppercase.
   All keys are strings. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name" \/ k = "city".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Last_Name", "Doe"); ("Age", "35"); 
     ("city", "Newor$50,00ange York"); ("Income", "$50,000"); 
     ("FIRST_NAME", "Jane"); ("Incoome", "oJohn")] false.
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
    + (* Case: all_lower is true *)
      (* We know "Last_Name" is in the list and is not lower. *)
      (* "Last_Name" is the 2nd element. *)
      inversion H_lower as [| k1 l1 H1 H_rest1]; subst.
      inversion H_rest1 as [| k2 l2 H2 H_rest2]; subst.
      destruct H2 as [_ H_is_lower].
      (* H_is_lower: is_lower_test "Last_Name" *)
      unfold is_lower_test in H_is_lower.
      destruct H_is_lower as [H_eq | H_eq]; discriminate H_eq.
      
    + (* Case: all_upper is true *)
      (* We know "first_name" is in the list and is not upper. *)
      (* "first_name" is the 1st element. *)
      inversion H_upper as [| k1 l1 H1 H_rest1]; subst.
      destruct H1 as [_ H_is_upper].
      (* H_is_upper: is_upper_test "first_name" *)
      unfold is_upper_test in H_is_upper.
      discriminate H_is_upper.
Qed.