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
   Keys are "1", "2", "3", "Income".
   In this context, digits are neither lower nor upper, 
   and "Income" is mixed case, so neither lower nor upper. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := False.

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("1", "apple"); ("2", "orange"); ("3", "cherry"); ("Income", "chINCEOMEOerry")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> (all_lower \/ all_upper) *)
    intros H.
    inversion H. (* Contradiction: false <> true *)
        
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case all_lower *)
      (* H_lower implies the first element "1" is lower, which is false *)
      inversion H_lower as [| x l H_head H_tail].
      destruct H_head as [_ H_low].
      unfold is_lower_test in H_low.
      contradiction.
    + (* Case all_upper *)
      (* H_upper implies the first element "1" is upper, which is false *)
      inversion H_upper as [| x l H_head H_tail].
      destruct H_head as [_ H_up].
      unfold is_upper_test in H_up.
      contradiction.
Qed.