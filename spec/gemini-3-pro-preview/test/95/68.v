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
Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "last_name" \/ k = "age" \/ k = "city" \/ k = "income".
Definition is_upper_test (k : key_impl) : Prop := False.

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("last_name", "Doe"); ("age", "35"); ("city", "oNew YorNk"); ("income", "$50,000"); ("Newage", "2,000")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros [H_lower | H_upper].
    + inversion H_lower as [| x1 l1 H1 H_tail1]; subst.
      destruct H1 as [_ H1].
      inversion H_tail1 as [| x2 l2 H2 H_tail2]; subst.
      destruct H2 as [_ H2].
      inversion H_tail2 as [| x3 l3 H3 H_tail3]; subst.
      destruct H3 as [_ H3].
      inversion H_tail3 as [| x4 l4 H4 H_tail4]; subst.
      destruct H4 as [_ H4].
      inversion H_tail4 as [| x5 l5 H5 H_tail5]; subst.
      destruct H5 as [_ H5].
      inversion H_tail5 as [| x6 l6 H6 H_tail6]; subst.
      destruct H6 as [_ H6].
      unfold is_lower_test in H6.
      repeat (destruct H6 as [H_eq | H6]; [discriminate H_eq | ]).
      discriminate H6.
    + inversion H_upper as [| x1 l1 H1 H_tail1]; subst.
      destruct H1 as [_ H1].
      unfold is_upper_test in H1.
      contradiction.
Qed.