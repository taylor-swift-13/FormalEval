Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
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

Example test_next_smallest_2 :
  problem_90_spec [4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z] None.
Proof.
  unfold problem_90_spec.
  intros H.
  destruct H as [x [y [Hx [Hy Hneq]]]].
  simpl in Hx.
  simpl in Hy.
  destruct Hx as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]];
  destruct Hy as [H' | [H' | [H' | [H' | [H' | [H' | [H' | [H' | H']]]]]]]];
  subst; try contradiction; try lia.
Qed.