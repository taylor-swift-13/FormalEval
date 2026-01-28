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

(* Sum type to handle mixed value types (string and int) in the dictionary *)
Inductive val_sum := 
| VStr (s : string)
| VInt (n : nat).

Definition val_impl := val_sum.

(* Predicates for the specific test case:
   Keys are "first_name", "Age", "FIRST_NAME".
   "first_name" is lowercase.
   "Age" is mixed case (Title case).
   "FIRST_NAME" is uppercase. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", VStr "John"); ("Age", VInt 35); ("FIRST_NAME", VStr "Jane")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. discriminate H.
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all keys are lower *)
      (* Deconstruct Forall to reach "Age" *)
      inversion H_lower as [| k l H_first H_rest]. subst.
      inversion H_rest as [| k2 l2 H_age H_rest2]. subst.
      destruct H_age as [_ H_age_lower].
      (* H_age_lower implies "Age" is lower, which contradicts is_lower_test *)
      unfold is_lower_test in H_age_lower.
      discriminate H_age_lower.
    + (* Case: all keys are upper *)
      (* Deconstruct Forall to check "first_name" *)
      inversion H_upper as [| k l H_first H_rest]. subst.
      destruct H_first as [_ H_first_upper].
      (* H_first_upper implies "first_name" is upper, which contradicts is_upper_test *)
      unfold is_upper_test in H_first_upper.
      discriminate H_first_upper.
Qed.