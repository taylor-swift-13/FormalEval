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
   Keys are "PI", "IPI", "Johageage", "JohaJgeage", "PPI". *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := 
  k = "PI" \/ k = "IPI" \/ k = "PPI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "3.14159"); 
     ("IPI", "2.6443947966293897"); 
     ("Johageage", "2.9360614575298136"); 
     ("JohaJgeage", "3.14159"); 
     ("PPI", "2.9360614575298136")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros [H_lower | H_upper].
    + (* Case: all keys are lower *)
      inversion H_lower; subst.
      destruct H1 as [_ H_is_lower].
      unfold is_lower_test in H_is_lower.
      contradiction.
    + (* Case: all keys are upper *)
      inversion H_upper; subst. (* PI *)
      inversion H2; subst. (* IPI *)
      inversion H4; subst. (* Johageage *)
      destruct H5 as [_ H_is_upper].
      unfold is_upper_test in H_is_upper.
      destruct H_is_upper as [H_eq | [H_eq | H_eq]]; discriminate.
Qed.