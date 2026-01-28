Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* Definition provided in the specification *)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

(* Pre-condition definition *)
Definition problem_29_pre (input : list string) : Prop := True.

(* Specification definition *)
Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

(* Test case: input = ["zzz"; "zzz"; "zzz"], substring = "z", output = ["zzz"; "zzz"; "zzz"] *)
Example problem_29_test : problem_29_spec ["zzz"; "zzz"; "zzz"] "z" ["zzz"; "zzz"; "zzz"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    simpl.
    left. split. reflexivity.
    left. split. reflexivity.
    left. split. reflexivity.
    simpl. trivial.
  - (* Part 2: forall s, In s output <-> In s input /\ prefix substring s = true *)
    intros s.
    split.
    + (* Forward: In s output -> In s input /\ prefix ... *)
      intros H.
      split.
      * (* In s output -> In s input *)
        apply H.
      * (* In s output -> prefix substring s = true *)
        simpl in H.
        destruct H as [H1 | [H2 | [H3 | H4]]].
        -- subst s. reflexivity.
        -- subst s. reflexivity.
        -- subst s. reflexivity.
        -- contradiction.
    + (* Backward: In s input /\ prefix ... -> In s output *)
      intros [H_in H_prefix].
      apply H_in.
Qed.