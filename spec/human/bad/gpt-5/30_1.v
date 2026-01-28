Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition is_positive (r : R) : Prop :=
  r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example problem_30_test :
  problem_30_spec [IZR (-1%Z); IZR (-2%Z); IZR (4%Z); IZR (5%Z); IZR (6%Z)]
                  [IZR (4%Z); IZR (5%Z); IZR (6%Z)].
Proof.
  split.
  - simpl.
    right. (* skip -1 *)
    simpl.
    right. (* skip -2 *)
    simpl.
    left. split. (* match 4 *)
    + reflexivity.
    + simpl.
      left. split. (* match 5 *)
      * reflexivity.
      * simpl.
        left. split. (* match 6 *)
        -- reflexivity.
        -- simpl. exact I.
  - intros r. split.
    + intros Hout.
      simpl in Hout.
      destruct Hout as [H4 | Hout].
      * subst r. split.
        -- simpl. right. right. left. reflexivity.
        -- lra.
      * destruct Hout as [H5 | H6].
        -- subst r. split.
           ++ simpl. right. right. right. left. reflexivity.
           ++ lra.
        -- subst r. split.
           ++ simpl. right. right. right. right. left. reflexivity.
           ++ lra.
    + intros [Hin Hpos].
      simpl in Hin.
      destruct Hin as [Hneg1 | Hin].
      * subst r. exfalso. lra.
      * destruct Hin as [Hneg2 | Hin].
        -- subst r. exfalso. lra.
        -- destruct Hin as [H4 | Hin].
           ++ subst r. simpl. left. reflexivity.
           ++ destruct Hin as [H5 | H6].
              ** subst r. simpl. right. left. reflexivity.
              ** subst r. simpl. right. right. left. reflexivity.
Qed.