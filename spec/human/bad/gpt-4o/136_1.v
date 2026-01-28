Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint largest_negative (lst : list Z) : option Z :=
  match lst with
  | [] => None
  | x :: xs =>
      let a := largest_negative xs in
      if x <? 0 then
        match a with
        | Some z => Some (Z.max x z)
        | None => Some x
        end
      else a
  end.

Fixpoint smallest_positive (lst : list Z) : option Z :=
  match lst with
  | [] => None
  | x :: xs =>
      let b := smallest_positive xs in
      if 0 <? x then
        match b with
        | Some z => Some (Z.min x z)
        | None => Some x
        end
      else b
  end.

Definition largest_smallest_integers (lst : list Z) : option Z * option Z :=
  (largest_negative lst, smallest_positive lst).

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

Example test_largest_smallest_integers_1 :
  problem_136_spec [2; 4; 1; 3; 5; 7] (None, Some 1).
Proof.
  unfold problem_136_spec.
  simpl.
  split.
  - unfold is_largest_negative. intros x H. inversion H. inversion H0.
  - unfold is_smallest_positive. split.
    + lia.
    + split. simpl. left. reflexivity.
    + intros x Hx H. destruct Hx as [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | [] ]]]]]]; try lia.
      * rewrite H2 in H. easy.
Qed.