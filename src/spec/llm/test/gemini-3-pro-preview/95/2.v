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
   'p' is lowercase, 'A' and 'B' are uppercase. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "p".
Definition is_upper_test (k : key_impl) : Prop := k = "A" \/ k = "B".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("p", "pineapple"); ("A", "banana"); ("B", "banana")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all_lower is true *)
      (* Deconstruct Forall to reach the second element "A" which is not lower *)
      inversion H_lower as [| k1 l1 H_p H_tail1]. subst.
      inversion H_tail1 as [| k2 l2 H_A H_tail2]. subst.
      destruct H_A as [_ H_A_lower].
      unfold is_lower_test in H_A_lower.
      (* "A" = "p" is False *)
      inversion H_A_lower.
      
    + (* Case: all_upper is true *)
      (* Deconstruct Forall to reach the first element "p" which is not upper *)
      inversion H_upper as [| k1 l1 H_p H_tail1]. subst.
      destruct H_p as [_ H_p_upper].
      unfold is_upper_test in H_p_upper.
      (* "p" = "A" \/ "p" = "B" is False *)
      destruct H_p_upper as [H_eqA | H_eqB]; inversion H_eqA || inversion H_eqB.
Qed.