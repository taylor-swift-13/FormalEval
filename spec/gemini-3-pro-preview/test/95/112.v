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
(* None of the keys are all lowercase *)
Definition is_lower_test (k : key_impl) : Prop := False.
(* Only "PI" is all uppercase *)
Definition is_upper_test (k : key_impl) : Prop := k = "PI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "1.7300435058060522"); 
     ("New YorkLAST_NAMEPI", "2.6189164796316335"); 
     ("cItIY", "2.6443947966293897"); 
     ("New YorkLASTcity_NAMEPI", "2.3210819853008124"); 
     ("NNew YorkLASTcity_NAMEPIew York", "2.2786871475765835")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros [H_lower | H_upper].
    + (* Case: all_lower *)
      inversion H_lower as [| k l H_head H_tail].
      destruct H_head as [_ H_low].
      unfold is_lower_test in H_low.
      contradiction.
    + (* Case: all_upper *)
      inversion H_upper as [| k1 l1 H_head1 H_tail1].
      (* First element "PI" is upper, so we check the tail *)
      inversion H_tail1 as [| k2 l2 H_head2 H_tail2].
      (* Second element is "New YorkLAST_NAMEPI" *)
      destruct H_head2 as [_ H_up2].
      unfold is_upper_test in H_up2.
      discriminate H_up2.
Qed.