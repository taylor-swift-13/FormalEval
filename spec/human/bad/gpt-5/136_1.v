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

Example problem_136_test :
  problem_136_spec [2%Z; 4%Z; 1%Z; 3%Z; 5%Z; 7%Z] (None, Some 1%Z).
Proof.
  unfold problem_136_spec; simpl.
  split.
  - (* No negative integers in the list *)
    unfold is_largest_negative; simpl.
    intros x HIn; unfold not; intros Hlt.
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia |].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia |].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia |].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia |].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia |].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia |].
    inversion HIn.
  - (* Smallest positive is 1 *)
    unfold is_smallest_positive; simpl.
    repeat split.
    + lia.
    + simpl. right. right. left. reflexivity.
    + intros x HIn Hpos.
      simpl in HIn.
      destruct HIn as [Hx|HIn]; [subst; lia |].
      simpl in HIn.
      destruct HIn as [Hx|HIn]; [subst; lia |].
      simpl in HIn.
      destruct HIn as [Hx|HIn]; [subst; lia |].
      simpl in HIn.
      destruct HIn as [Hx|HIn]; [subst; lia |].
      simpl in HIn.
      destruct HIn as [Hx|HIn]; [subst; lia |].
      simpl in HIn.
      destruct HIn as [Hx|HIn]; [subst; lia |].
      inversion HIn.
Qed.