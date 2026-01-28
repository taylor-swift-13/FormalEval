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

(* None of the keys in the input are all lowercase *)
Definition is_lower_test (k : key_impl) : Prop := False.

(* Only "PI" is all uppercase in this input list *)
Definition is_upper_test (k : key_impl) : Prop := k = "PI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "1.7300435058060522"); 
     ("New YorkLAST_NAMEPI", "2.6189164796316335"); 
     ("cItIY", "2.6443947966293897"); 
     ("New YorkLAST_NALast_NammeMEPI", "0.8622214662877261")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. discriminate.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all_lower is true *)
      (* The first key is "PI". is_lower "PI" is False by definition. *)
      inversion H_lower; subst.
      destruct H1 as [_ H_low].
      unfold is_lower_test in H_low.
      contradiction.
      
    + (* Case: all_upper is true *)
      (* The first key "PI" is upper, so we step through it. *)
      inversion H_upper; subst.
      (* The second key "New YorkLAST_NAMEPI" is NOT upper. *)
      inversion H2; subst.
      destruct H3 as [_ H_up].
      unfold is_upper_test in H_up.
      (* "New YorkLAST_NAMEPI" = "PI" is False *)
      discriminate.
Qed.