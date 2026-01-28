Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_90_pre (l : list Z) : Prop := True.

Definition problem_90_spec (l : list Z) (res : option Z) : Prop :=
  match res with
  | Some z =>
    exists s1,
      In s1 l /\
      (forall x, In x l -> s1 <= x) /\
      In z l /\
      s1 < z /\
      (forall y, In y l -> s1 < y -> z <= y)
  | None =>
    ~ (exists x y, In x l /\ In y l /\ x <> y)
  end.

Example test_problem_90 : problem_90_spec [1; 2; 3; 4; 5] (Some 2).
Proof.
  unfold problem_90_spec.
  exists 1.
  repeat split.
  - (* 1. Prove s1 is in l *)
    simpl. left. reflexivity.
  - (* 2. Prove s1 is the minimum *)
    intros x H. simpl in H.
    repeat destruct H as [H|H]; subst; try lia.
  - (* 3. Prove z is in l *)
    simpl. right. left. reflexivity.
  - (* 4. Prove s1 < z *)
    lia.
  - (* 5. Prove z is the second smallest *)
    intros y H_in H_gt. simpl in H_in.
    repeat destruct H_in as [H_in|H_in]; subst; try lia.
Qed.