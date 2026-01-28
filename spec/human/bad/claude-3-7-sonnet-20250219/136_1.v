Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* a 是 lst 中最大的负整数（Some z）或不存在负整数（None） *)
Definition is_largest_negative (lst : list Z) (a : option Z) : Prop :=
  match a with
  | Some z => z < 0 /\ In z lst /\ (forall x, In x lst -> x < 0 -> x <= z)
  | None   => forall x, In x lst -> ~(x < 0)
  end.

(* b 是 lst 中最小的正整数（Some z）或不存在正整数（None） *)
Definition is_smallest_positive (lst : list Z) (b : option Z) : Prop :=
  match b with
  | Some z => z > 0 /\ In z lst /\ (forall x, In x lst -> x > 0 -> z <= x)
  | None   => forall x, In x lst -> ~(x > 0)
  end.

Definition problem_136_pre (lst : list Z) : Prop := True.

Definition problem_136_spec (lst : list Z) (res : option Z * option Z) : Prop :=
  let (a, b) := res in
  is_largest_negative lst a /\ is_smallest_positive lst b.

Example test_case_1 :
  problem_136_spec [2;4;1;3;5;7] (None, Some 1).
Proof.
  unfold problem_136_spec.
  simpl.
  split.
  - (* is_largest_negative lst None *)
    unfold is_largest_negative.
    intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; try lia).
  - (* is_smallest_positive lst (Some 1) *)
    unfold is_smallest_positive.
    split.
    + lia.
    + split.
      * simpl. right. right. left. reflexivity.
      * intros x Hx_in Hx_pos.
        simpl in Hx_in.
        destruct Hx_in as [H1|Htail].
        -- subst x. lia.
        -- destruct Htail as [H2|Htail2].
           ++ subst x. lia.
           ++ destruct Htail2 as [H3|Htail3].
              ** subst x. lia.
              ** destruct Htail3 as [H4|Htail4].
                 --- subst x. lia.
                 --- destruct Htail4 as [H5|H6].
                     +++ subst x. lia.
                     +++ (* contradiction: no more elements *)
                         inversion H6.
Qed.