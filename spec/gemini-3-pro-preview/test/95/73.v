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
   'orange' is lower, 'LAST_NAME' is upper, 'Dooe' is mixed. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "orange".
Definition is_upper_test (k : key_impl) : Prop := k = "LAST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("orange", "JoDooehn"); ("Dooe", "JoDooehhn"); ("LAST_NAME", "NK")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros [H_lower | H_upper].
    + (* Case: Assume all keys are lower *)
      (* keys = ["orange"; "Dooe"; "LAST_NAME"] *)
      inversion H_lower; subst.
      inversion H2; subst. (* Look at second element "Dooe" *)
      destruct H3 as [_ H_dooe_lower].
      unfold is_lower_test in H_dooe_lower.
      (* "Dooe" = "orange" is False *)
      discriminate H_dooe_lower.
    + (* Case: Assume all keys are upper *)
      inversion H_upper; subst. (* Look at first element "orange" *)
      destruct H1 as [_ H_orange_upper].
      unfold is_upper_test in H_orange_upper.
      (* "orange" = "LAST_NAME" is False *)
      discriminate H_orange_upper.
Qed.