Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_largest_negative (lst : list Z) (a : option Z) : Prop :=
  match a with
  | Some z => z < 0 /\ In z lst /\ (forall x, In x lst -> x < 0 -> x <= z)
  | None   => forall x, In x lst -> ~(x < 0)
  end.

Definition is_smallest_positive (lst : list Z) (b : option Z) : Prop :=
  match b with
  | Some z => z > 0 /\ In z lst /\ (forall x, In x lst -> x > 0 -> z <= x)
  | None   => forall x, In x lst -> ~(x > 0)
  end.

Definition problem_136_pre (lst : list Z) : Prop := True.

Definition problem_136_spec (lst : list Z) (res : option Z * option Z) : Prop :=
  let (a, b) := res in
  is_largest_negative lst a /\ is_smallest_positive lst b.

Example test_case_2 : problem_136_spec [1%Z; -5%Z; 9%Z; -8%Z; -4%Z; 5%Z; 1%Z] (Some (-4)%Z, Some 1%Z).
Proof.
  unfold problem_136_spec.
  split.
  - unfold is_largest_negative.
    split.
    + lia.
    + split.
      * simpl. right. right. right. right. left. reflexivity.
      * intros x Hin Hneg.
        simpl in Hin.
        destruct Hin as [H | [H | [H | [H | [H | [H | [H | H]]]]]]];
          subst; lia.
  - unfold is_smallest_positive.
    split.
    + lia.
    + split.
      * simpl. left. reflexivity.
      * intros x Hin Hpos.
        simpl in Hin.
        destruct Hin as [H | [H | [H | [H | [H | [H | [H | H]]]]]]];
          subst; lia.
Qed.