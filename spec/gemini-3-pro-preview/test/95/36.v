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

(* Predicates for the specific test case *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME" \/ k = "LAST_NAME" \/ k = "AGE" \/ k = "CITY" \/ k = "INCOME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("FIRST_NAME", "John"); ("LAST_NAME", "DOE"); ("AGE", "35"); ("CITY", "NK"); ("INCOME", "$50,000"); ("1", "35")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros [H_lower | H_upper].
    + inversion H_lower; subst.
      destruct H1 as [_ H_false].
      unfold is_lower_test in H_false.
      contradiction.
    + inversion H_upper; subst.
      inversion H2; subst.
      inversion H4; subst.
      inversion H6; subst.
      inversion H8; subst.
      inversion H10; subst.
      destruct H11 as [_ H_fail].
      unfold is_upper_test in H_fail.
      repeat match goal with 
      | [ H : _ \/ _ |- _ ] => destruct H 
      end; discriminate.
Qed.