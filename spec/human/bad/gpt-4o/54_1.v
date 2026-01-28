Require Import List Ascii String.
Open Scope string_scope.

(* Helper function to convert a string to a list of ascii *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: list_ascii_of_string s'
  end.

(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example problem_54_test : problem_54_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  unfold problem_54_spec.
  simpl.
  split; intros H c; split; intros H_in.
  - (* Forward direction: In c list_s0 -> In c list_s1 *)
    (* Check each character in "eabcdzzzz" and show it is in "dddzzzzzzzddeddabc" *)
    destruct (ascii_dec c "e") as [He|Hne].
    + subst. apply in_or_app. right. apply in_or_app. left. apply in_eq.
    + destruct (ascii_dec c "a") as [Ha|Hna].
      * subst. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_eq.
      * destruct (ascii_dec c "b") as [Hb|Hnb].
        -- subst. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_cons. apply in_eq.
        -- destruct (ascii_dec c "c") as [Hc|Hnc].
           ++ subst. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_cons. apply in_cons. apply in_eq.
           ++ destruct (ascii_dec c "d") as [Hd|Hnd].
              ** subst. apply in_or_app. left. apply in_eq.
              ** destruct (ascii_dec c "z") as [Hz|Hnz].
                 --- subst. apply in_or_app. right. apply in_or_app. left. apply in_cons. apply in_eq.
                 --- exfalso. apply H_in. assumption.
  - (* Backward direction: In c list_s1 -> In c list_s0 *)
    (* Check each character in "dddzzzzzzzddeddabc" and show it is in "eabcdzzzz" *)
    destruct (ascii_dec c "d") as [Hd|Hnd].
    + subst. apply in_or_app. right. apply in_or_app. left. apply in_cons. apply in_eq.
    + destruct (ascii_dec c "e") as [He|Hne].
      * subst. apply in_or_app. left. apply in_eq.
      * destruct (ascii_dec c "a") as [Ha|Hna].
        -- subst. apply in_or_app. right. apply in_or_app. right. apply in_eq.
        -- destruct (ascii_dec c "b") as [Hb|Hnb].
           ++ subst. apply in_or_app. right. apply in_or_app. right. apply in_cons. apply in_eq.
           ++ destruct (ascii_dec c "c") as [Hc|Hnc].
              ** subst. apply in_or_app. right. apply in_or_app. right. apply in_cons. apply in_cons. apply in_eq.
              ** destruct (ascii_dec c "z") as [Hz|Hnz].
                 --- subst. apply in_or_app. right. apply in_or_app. left. apply in_eq.
                 --- exfalso. apply H_in. apply in_or_app. right. apply in_or_app. right. apply in_cons. apply in_cons. apply in_cons. apply in_eq.
Qed.