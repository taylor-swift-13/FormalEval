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
   Keys are "2", "3", "Income", "$50,000", "Inconme".
   None of these are considered purely lowercase or uppercase in the Python sense 
   (numbers/symbols return False, mixed case returns False). *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := False.

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("2", "banana"); ("3", "cherry"); ("Income", "New York"); ("$50,000", "chrerry"); ("Inconme", "bana")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  (* This simplifies to: False <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H.
    discriminate H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [Hlow | Hup].
    + (* Case all_lower *)
      (* Hlow implies that the first element "2" satisfies is_lower, which is False *)
      inversion Hlow as [| x l Hhead Htail].
      destruct Hhead as [_ Hfalse].
      contradiction.
    + (* Case all_upper *)
      (* Hup implies that the first element "2" satisfies is_upper, which is False *)
      inversion Hup as [| x l Hhead Htail].
      destruct Hhead as [_ Hfalse].
      contradiction.
Qed.