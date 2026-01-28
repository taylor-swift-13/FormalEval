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
   'PI' is upper. 'New YorkLAST_NAMEPI' and 'cItIY' are mixed (neither all lower nor all upper).
   Therefore, is_lower is false for all. is_upper is true only for 'PI'. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := k = "PI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "1.7300435058060522"); ("New YorkLAST_NAMEPI", "2.6189164796316335"); ("cItIY", "2.6443947966293897")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> (all_lower \/ all_upper) *)
    intros H.
    discriminate H.
        
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case all_lower *)
      (* We have Forall is_lower on the list. The first element is "PI". *)
      inversion H_lower as [| k l H_head H_tail]. subst.
      destruct H_head as [_ H_is_lower].
      (* is_lower_test "PI" is False *)
      unfold is_lower_test in H_is_lower.
      contradiction.
      
    + (* Case all_upper *)
      (* We have Forall is_upper on the list. *)
      inversion H_upper as [| k l H_head H_tail]. subst.
      (* Head is "PI", which is upper (ok). Check tail. *)
      inversion H_tail as [| k2 l2 H_head2 H_tail2]. subst.
      (* Next element k2 is "New YorkLAST_NAMEPI". *)
      destruct H_head2 as [_ H_is_upper2].
      unfold is_upper_test in H_is_upper2.
      (* "New YorkLAST_NAMEPI" = "PI" is false. *)
      discriminate H_is_upper2.
Qed.