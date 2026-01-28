Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example problem_29_test_case :
  problem_29_spec ["aa"%string; "a"%string] ("a"%string) ["aa"%string; "a"%string].
Proof.
  unfold problem_29_spec.
  split.
  - simpl. left. split.
    + reflexivity.
    + simpl. left. split.
      * reflexivity.
      * simpl. exact I.
  - intros s; split.
    + intros HIn. split.
      * exact HIn.
      * simpl in HIn.
        destruct HIn as [Hs_aa | [Hs_a | Hf]].
        -- subst. compute. reflexivity.
        -- subst. compute. reflexivity.
        -- exfalso. exact Hf.
    + intros [Hin Hpref].
      exact Hin.
Qed.