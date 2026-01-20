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
   'p', '5', 'a' are strings.
   'p' and 'a' are lowercase.
   '5' is not lowercase.
   None are uppercase. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "p" \/ k = "a".
Definition is_upper_test (k : key_impl) : Prop := False.

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("p", "pineapple"); ("5", "banana"); ("a", "apple")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> (all_lower \/ all_upper) *)
    intros H.
    inversion H. (* Contradiction: false <> true *)
        
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all_lower. We must show this is impossible because '5' is not lower. *)
      (* H_lower : Forall ... ["p"; "5"; "a"] *)
      inversion H_lower as [| ? ? Hp_props H5a_props]; subst.
      (* H5a_props : Forall ... ["5"; "a"] *)
      inversion H5a_props as [| ? ? H5_props Ha_props]; subst.
      (* H5_props : is_str "5" /\ is_lower "5" *)
      destruct H5_props as [_ H5_lower].
      unfold is_lower_test in H5_lower.
      (* H5_lower : "5" = "p" \/ "5" = "a" *)
      destruct H5_lower as [C | C]; inversion C.
      
    + (* Case: all_upper. Impossible because 'p' is not upper. *)
      (* H_upper : Forall ... ["p"; "5"; "a"] *)
      inversion H_upper as [| ? ? Hp_props H5a_props]; subst.
      destruct Hp_props as [_ Hp_upper].
      unfold is_upper_test in Hp_upper.
      contradiction.
Qed.