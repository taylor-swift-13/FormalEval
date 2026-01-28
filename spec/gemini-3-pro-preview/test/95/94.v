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
Definition val_impl := nat.

(* Predicates for the specific test case: 
   'Age' is a string, but it is mixed case (neither all lower nor all upper). *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := False.

Example test_check_dict_case_fail : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("Age", 35)] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H.
    discriminate H.
  - intros [H | H].
    + inversion H; subst.
      destruct H2 as [_ HLow].
      unfold is_lower_test in HLow.
      contradiction.
    + inversion H; subst.
      destruct H2 as [_ HUp].
      unfold is_upper_test in HUp.
      contradiction.
Qed.