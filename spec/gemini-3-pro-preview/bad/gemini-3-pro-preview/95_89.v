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
   Keys are "FIRST_NAME", "AGE", "CITY", "COME", "John".
   None are all lowercase.
   First four are uppercase, "John" is mixed. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME" \/ k = "AGE" \/ k = "CITY" \/ k = "COME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("FIRST_NAME", "John"); ("AGE", "35"); ("CITY", "NEW YORK"); ("COME", "$50,0000"); ("John", "year")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all keys are lower *)
      (* The first key is "FIRST_NAME", which is not lower. *)
      inversion H_lower; subst.
      destruct H1 as [_ H_low].
      unfold is_lower_test in H_low.
      contradiction.
      
    + (* Case: all keys are upper *)
      (* Keys: FIRST_NAME, AGE, CITY, COME, John *)
      (* We traverse the list to find the violation at "John" *)
      inversion H_upper; subst. (* FIRST_NAME *)
      inversion H2; subst.      (* AGE *)
      inversion H3; subst.      (* CITY *)
      inversion H4; subst.      (* COME *)
      inversion H5; subst.      (* John *)
      
      destruct H1 as [_ H_up].
      unfold is_upper_test in H_up.
      
      (* H_up asserts "John" is one of the upper keys. We disprove each equality. *)
      destruct H_up as [H_eq | H_up]; [discriminate H_eq |].
      destruct H_up as [H_eq | H_up]; [discriminate H_eq |].
      destruct H_up as [H_eq | H_up]; [discriminate H_eq |].
      discriminate H_up.
Qed.