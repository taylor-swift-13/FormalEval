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
   'Name', 'Age', 'City' are strings, but mixed case. *)
Definition is_str_test (k : key_impl) : Prop := True.
(* "Name", "Age", "City" contain uppercase letters, so is_lower is false. *)
Definition is_lower_test (k : key_impl) : Prop := False.
(* "Name", "Age", "City" contain lowercase letters, so is_upper is false. *)
Definition is_upper_test (k : key_impl) : Prop := False.

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("Name", "John"); ("Age", "36"); ("City", "Houston")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H.
    discriminate H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case all_lower *)
      (* Forall P (x :: l) -> P x /\ Forall P l *)
      inversion H_lower.
      (* H1 is P "Name", which is (is_str "Name" /\ is_lower "Name") *)
      destruct H1 as [_ H_low].
      unfold is_lower_test in H_low.
      contradiction.
    + (* Case all_upper *)
      inversion H_upper.
      destruct H1 as [_ H_up].
      unfold is_upper_test in H_up.
      contradiction.
Qed.