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
   keys: "PI", "New YorkLAST_NAMEPI", "cItIY", "I", "8PI", "JohJIncomeyeyarohnn"
   is_lower is false for all.
   is_upper is true only for "PI", "I", "8PI".
*)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := 
  k = "PI" \/ k = "I" \/ k = "8PI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "1.7300435058060522"); 
     ("New YorkLAST_NAMEPI", "2.6189164796316335"); 
     ("cItIY", "2.6443947966293897"); 
     ("I", "2.9360614575298136"); 
     ("8PI", "2.2268929884240265"); 
     ("JohJIncomeyeyarohnn", "1.9949170779000351")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. discriminate.
        
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case all_lower *)
      (* The first key "PI" must be lower, but is_lower_test is False *)
      inversion H_lower as [| ? ? H_head H_tail]; subst.
      destruct H_head as [_ H_false].
      contradiction.
      
    + (* Case all_upper *)
      (* The second key "New YorkLAST_NAMEPI" must be upper, but it is not in is_upper_test *)
      (* H_upper says Forall ... for the whole list *)
      inversion H_upper as [| ? ? H_head1 H_tail1]; subst. (* Head "PI" *)
      inversion H_tail1 as [| ? ? H_head2 H_tail2]; subst. (* Head "New York..." *)
      
      (* Extract the property for "New York..." *)
      destruct H_head2 as [_ H_NY_upper].
      
      (* Unfold definition to check validity *)
      unfold is_upper_test in H_NY_upper.
      
      (* H_NY_upper is a disjunction of equalities. We show all are false. *)
      destruct H_NY_upper as [H_eq | [H_eq | H_eq]]; discriminate.
Qed.