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
   'PI' is upper, 'new yorrk' is lower. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "new yorrk".
Definition is_upper_test (k : key_impl) : Prop := k = "PI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "1.7300435058060522"); ("new yorrk", "2.2762868739904514")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> (all_lower \/ all_upper) *)
    intros H.
    inversion H.
        
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case all_lower: Forall fails on "PI" *)
      inversion H_lower as [| x l Hhead Htail].
      destruct Hhead as [_ Hlow].
      unfold is_lower_test in Hlow.
      inversion Hlow.
    + (* Case all_upper: Forall fails on "new yorrk" *)
      inversion H_upper as [| x l Hhead Htail].
      inversion Htail as [| x2 l2 Hhead2 Htail2].
      destruct Hhead2 as [_ Hup].
      unfold is_upper_test in Hup.
      inversion Hup.
Qed.