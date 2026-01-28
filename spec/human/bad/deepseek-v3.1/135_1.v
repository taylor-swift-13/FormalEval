Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition drop_at (lst : list Z) (k : nat) : Prop :=
  (1 <= k)%nat /\ (k < length lst)%nat /\
  match nth_error lst k, nth_error lst (k - 1) with
  | Some y, Some x => (y < x)%Z
  | _, _ => False
  end.

Definition problem_135_spec (lst : list Z) (r : Z) : Prop :=
  (r = -1 /\ (forall k, ~ drop_at lst k))
  \/
  (exists k : nat,
      r = Z.of_nat k /\
      drop_at lst k /\
      (forall j : nat, drop_at lst j -> (j <= k)%nat)).

Example test_case_1 : problem_135_spec [1; 2; 4; 3; 5] 3.
Proof.
  right.
  exists 3%nat.
  repeat split.
  - reflexivity.
  - unfold drop_at.
    repeat split; try lia.
    + simpl; auto.
    + simpl.
      rewrite Nat.sub_0_r.
      simpl.
      lia.
  - intros j H.
    unfold drop_at in H.
    destruct H as [Hle [Hlt Hnth]].
    (* Check all possible indices where drop_at could hold *)
    destruct j as [|j]; [lia|].
    destruct j as [|j]; [lia|].
    destruct j as [|j]; [lia|].
    destruct j as [|j]; [lia|].
    (* j = 4 or higher, but our list only has length 5, so j < 5 *)
    assert (j < 4)%nat by lia.
    destruct j; [lia|].
    destruct j; [lia|].
    destruct j; [lia|].
    lia.
Qed.