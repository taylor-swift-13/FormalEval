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

(* Only "first_name" and "city" are lowercase in the input *)
Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "city".

(* Only "FIRST_NAME" is uppercase in the input *)
Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME".

Definition test_dict : list (key_impl * val_impl) := [
  ("first_name", "John"); 
  ("Last_Name", "Doe"); 
  ("Age", "35"); 
  ("city", "Newor$50,00ange York"); 
  ("Income", "$50,000"); 
  ("FIRST_NAME", "Jane"); 
  ("Incoome", "oJohn"); 
  ("", "oJoh")
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
    + (* Refuting all_lower: "Last_Name" (2nd element) is not lower *)
      inversion H_lower; subst.
      inversion H2; subst.
      destruct H3 as [_ H_is_lower].
      unfold is_lower_test in H_is_lower.
      destruct H_is_lower as [C1 | C2]; discriminate.
    + (* Refuting all_upper: "first_name" (1st element) is not upper *)
      inversion H_upper; subst.
      destruct H1 as [_ H_is_upper].
      unfold is_upper_test in H_is_upper.
      discriminate.
Qed.