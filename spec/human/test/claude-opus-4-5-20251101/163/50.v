(* 引入所需的基础库 *)
Require Import Coq.Lists.List.      (* List 定义与操作 *)
Require Import Coq.Arith.Arith.      (* 算术相关，包含 min, max, le, lt 等 *)
Require Import Coq.Sorting.Sorted.  (* Sorted 定义 *)
Require Import Coq.Lists.SetoidList.  (* NoDup 定义 *)
Require Import Lia.
Import ListNotations.

Definition problem_163_pre (a b : nat) : Prop := a > 0 /\ b > 0.

Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.

Example test_generate_integers_300_5 :
  problem_163_spec 300 5 [6; 8].
Proof.
  unfold problem_163_spec.
  split; [| split].
  - intros d.
    simpl.
    split.
    + intros H.
      destruct H as [H | [H | H]].
      -- subst d. repeat split; try lia. exists 3. lia.
      -- subst d. repeat split; try lia. exists 4. lia.
      -- contradiction.
    + intros (Hmin & Hmax & Hlt10 & Heven).
      simpl in Hmin, Hmax.
      destruct Heven as [k Hk].
      subst d.
      assert (Hk_cases : k = 3 \/ k = 4) by lia.
      destruct Hk_cases as [Hk3 | Hk4].
      -- subst k. left. reflexivity.
      -- subst k. right. left. reflexivity.
  - repeat constructor; lia.
  - constructor.
    + simpl. intros [H | H]; lia.
    + constructor.
      -- simpl. intros H; lia.
      -- constructor.
Qed.