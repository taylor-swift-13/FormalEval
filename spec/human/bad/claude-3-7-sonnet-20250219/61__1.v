Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.

Inductive is_correctly_bracketed : list ascii -> Prop :=
  | cb_nil    : is_correctly_bracketed []
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("("%char :: l ++ [")"%char])
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

Definition problem_61_spec (brackets : list ascii) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

(* Auxiliary function to check correct bracketing with a counter *)
Fixpoint check_brackets (l : list ascii) (n : nat) : bool :=
  match l with
  | [] => match n with
          | 0 => true
          | _ => false
          end
  | c :: tl =>
    if ascii_dec c "("%char then
      check_brackets tl (S n)
    else if ascii_dec c ")"%char then
      match n with
      | 0 => false
      | S n' => check_brackets tl n'
      end
    else false
  end.

Definition correct_bracketing_bool (l : list ascii) : bool :=
  check_brackets l 0.

Example problem_61_example :
  let input := ["("%char; ")"%char] in
  problem_61_spec input (correct_bracketing_bool input).
Proof.
  unfold problem_61_spec, correct_bracketing_bool.
  simpl.
  split.
  - intros H. subst.
    (* We must show is_correctly_bracketed ["("; ")"] *)
    (* Since ["("; ")"] = "(" :: [] ++ [")"], *)
    (* By cb_nest with l = [] *)
    apply cb_nest.
    apply cb_nil.
  - intros H.
    (* We must show check_brackets ["("; ")"] 0 = true *)
    simpl.
    (* "(" = "(" -> check_brackets [] 1 *)
    (* check_brackets [] 1 = false *)
    (* Wait, but we have to show it is true *)
    (* So check_brackets ["("; ")"] 0 should be true *)
    (* Let's evaluate check_brackets ["("; ")"] 0 *)
    cbv beta.
    simpl.
    unfold ascii_dec.
    destruct (ascii_dec "("%char "("%char).
    + (* c = "(" *)
      simpl.
      destruct (ascii_dec ")"%char ")"%char).
      * simpl.
        destruct 1.
        simpl.
        reflexivity.
      * congruence.
    + congruence.
Qed.