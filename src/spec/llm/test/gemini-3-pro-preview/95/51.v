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
   'PI' and 'IPI' are upper case. 'Johageage' and 'JohaJgeage' are mixed.
   None are lower case. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := k = "PI" \/ k = "IPI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "3.14159"); ("IPI", "2.6443947966293897"); ("Johageage", "2.9360614575298136"); ("JohaJgeage", "3.14159")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations *)
  simpl.
  
  (* The goal is false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward: false = true -> ... *)
    intros H. discriminate H.
    
  - (* Backward: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case all_lower *)
      (* The first key "PI" is not lower, which contradicts H_lower *)
      inversion H_lower as [| k l H_PI_lower H_rest]; subst.
      destruct H_PI_lower as [_ H_false].
      unfold is_lower_test in H_false.
      contradiction.
      
    + (* Case all_upper *)
      (* We check keys until we find one that is not upper *)
      inversion H_upper as [| k1 l1 H_PI_upper H_rest1]; subst. (* "PI" is upper, OK *)
      inversion H_rest1 as [| k2 l2 H_IPI_upper H_rest2]; subst. (* "IPI" is upper, OK *)
      inversion H_rest2 as [| k3 l3 H_Joha_upper H_rest3]; subst. (* "Johageage" *)
      
      (* "Johageage" must be upper, but is_upper_test says it must be "PI" or "IPI" *)
      destruct H_Joha_upper as [_ H_fail].
      unfold is_upper_test in H_fail.
      destruct H_fail as [H_eq | H_eq]; discriminate H_eq.
Qed.