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

(* Keys: 'first_name', 'Last_Name', 'Age', 'city', 'Income', 'FIRST_NAME', '1', 'Incyellowome' *)
(* Only 'first_name' and 'city' are strictly lowercase in Python (contain cased chars and all are lower) *)
Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "city".

(* Only 'FIRST_NAME' is strictly uppercase *)
Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME".

(* Input dictionary as a list of pairs. Values are represented as strings. *)
Definition test_dict : list (key_impl * val_impl) := [
  ("first_name", "John"); 
  ("Last_Name", "Dooe"); 
  ("Age", "35"); 
  ("city", "New York"); 
  ("Income", "$50,000"); 
  ("FIRST_NAME", "Jane"); 
  ("1", "36"); 
  ("Incyellowome", "INCOMEJohn")
].

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    test_dict false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. discriminate H.
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all_lower assumed true. Refute it with "Last_Name". *)
      (* "first_name" is ok *)
      inversion H_lower as [| k1 l1 H1 H_tail1]; subst.
      (* "Last_Name" is NOT lower *)
      inversion H_tail1 as [| k2 l2 H2 H_tail2]; subst.
      destruct H2 as [_ H_ln_lower].
      unfold is_lower_test in H_ln_lower.
      destruct H_ln_lower as [H_eq | H_eq]; discriminate H_eq.
    + (* Case: all_upper assumed true. Refute it with "first_name". *)
      (* "first_name" is NOT upper *)
      inversion H_upper as [| k1 l1 H1 H_tail1]; subst.
      destruct H1 as [_ H_fn_upper].
      unfold is_upper_test in H_fn_upper.
      discriminate H_fn_upper.
Qed.