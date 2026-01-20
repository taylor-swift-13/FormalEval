Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

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

(* Concrete instantiation for the test case *)
Definition Key_ex := bool.
Definition Value_ex := nat.

Definition is_str_ex (_ : Key_ex) : Prop := True.
Definition is_lower_ex (_ : Key_ex) : Prop := True.
Definition is_upper_ex (_ : Key_ex) : Prop := False.

Definition dict_ex : list (Key_ex * Value_ex) := [(true, 0); (false, S 0)].
Definition res_ex : bool := true.

Example check_dict_case_test :
  check_dict_case_spec Key_ex Value_ex is_str_ex is_lower_ex is_upper_ex dict_ex res_ex.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros _. left.
    constructor.
    + split; constructor.
    + constructor.
      * split; constructor.
      * constructor.
  - intros _. reflexivity.
Qed.