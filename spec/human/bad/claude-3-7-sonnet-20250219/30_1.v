Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence (x :: xs) ys
  end.

Definition is_positive (r : R) : Prop := r > 0.

Definition problem_30_spec (input output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_get_positive :
  let input := [-1; -2; 4; 5; 6] in
  let output := [4; 5; 6] in
  problem_30_spec input output.
Proof.
  unfold problem_30_spec.
  split.

  - (* is_subsequence output input *)
    simpl is_subsequence.
    (* output = 4 :: 5 :: 6 :: [] *)
    (* input = -1 :: -2 :: 4 :: 5 :: 6 :: [] *)
    (* Show is_subsequence [4; 5; 6] [-1; -2; 4; 5; 6] *)
    right; (* skip -1 *)
    simpl is_subsequence.
    right; (* skip -2 *)
    simpl is_subsequence.
    left; split; [reflexivity|].
    simpl is_subsequence.
    left; split; [reflexivity|].
    simpl is_subsequence.
    left; split; [reflexivity|].
    simpl is_subsequence.
    exact I.

  - (* forall r, In r output <-> In r input /\ is_positive r *)
    intros r; split; intros H.

    + (* -> *)
      simpl in H.
      destruct H as [H_eq | [H_eq | [H_eq | H_false]]].
      * subst r; split.
        -- simpl; right; right; left; reflexivity.
        -- lra.
      * subst r; split.
        -- simpl; right; right; right; left; reflexivity.
        -- lra.
      * subst r; split.
        -- simpl; right; right; right; right; left; reflexivity.
        -- lra.
      * contradiction.

    + (* <- *)
      destruct H as [H_in H_pos].
      simpl.
      destruct (Rgt_dec r 0).
      * (* r > 0 *)
        destruct H_in as [H_eq | [H_eq | [H_eq | H_false]]].
        -- subst r; simpl; left; reflexivity.
        -- subst r; simpl; right; left; reflexivity.
        -- subst r; simpl; right; right; left; reflexivity.
        -- contradiction.
      * exfalso; lra.
Qed.