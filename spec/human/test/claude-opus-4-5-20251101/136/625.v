Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
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

(* 任意整数列表均可 *)
Definition problem_136_pre (lst : list Z) : Prop := True.

(* 最终 Spec：结果 res = (a, b) 当且仅当 a 是最大的负整数（或 None），b 是最小的正整数（或 None） *)
Definition problem_136_spec (lst : list Z) (res : option Z * option Z) : Prop :=
  let (a, b) := res in
  is_largest_negative lst a /\ is_smallest_positive lst b.

Example test_case_2 : problem_136_spec [-9%Z; -6%Z; -3%Z; -1%Z; -8%Z] (Some (-1%Z), None).
Proof.
  unfold problem_136_spec.
  split.
  - (* is_largest_negative [-9; -6; -3; -1; -8] (Some (-1)) *)
    unfold is_largest_negative.
    split.
    + lia.
    + split.
      * simpl. right. right. right. left. reflexivity.
      * intros x Hin Hneg.
        simpl in Hin.
        destruct Hin as [H | [H | [H | [H | [H | H]]]]];
          subst; lia.
  - (* is_smallest_positive [-9; -6; -3; -1; -8] None *)
    unfold is_smallest_positive.
    intros x Hin Hpos.
    simpl in Hin.
    destruct Hin as [H | [H | [H | [H | [H | H]]]]];
      subst; lia.
Qed.