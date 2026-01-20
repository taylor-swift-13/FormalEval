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

(* Only "first_name" and "city" are lower case *)
Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "city".

(* Only "FIRST_NAME" is upper case *)
Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME".

Definition test_dict : list (key_impl * val_impl) := [
  ("first_name", "John"); 
  ("Last_Name", "Dooe"); 
  ("Age", "35"); 
  ("city", "New York"); 
  ("Income", "$50,000"); 
  ("FIRST_NAME", "Jane"); 
  ("Incyellowome", "INCOMEJohn")
].

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    test_dict false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros [H_lower | H_upper].
    + (* Case: all_lower assumed true *)
      (* "Last_Name" is the second element and is not lower *)
      inversion H_lower; subst. (* first_name *)
      inversion H2; subst. (* Last_Name *)
      destruct H3 as [_ H_fail].
      unfold is_lower_test in H_fail.
      destruct H_fail as [H_eq | H_eq]; discriminate H_eq.
    + (* Case: all_upper assumed true *)
      (* "first_name" is the first element and is not upper *)
      inversion H_upper; subst. (* first_name *)
      destruct H1 as [_ H_fail].
      unfold is_upper_test in H_fail.
      discriminate H_fail.
Qed.