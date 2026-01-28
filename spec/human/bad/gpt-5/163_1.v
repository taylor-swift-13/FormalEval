(* 引入所需的基础库 *)
Require Import Coq.Lists.List.      (* List 定义与操作 *)
Require Import Coq.Arith.Arith.      (* 算术相关，包含 min, max, le, lt 等 *)
Require Import Coq.Sorting.Sorted.  (* Sorted 定义 *)
Require Import Coq.Lists.SetoidList.  (* NoDup 定义 *)
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* 输入为正整数 *)
Definition problem_163_pre (a b : nat) : Prop := a > 0 /\ b > 0.

Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.

Example problem_163_example_2_10 :
  problem_163_spec 2 10 [2;4;6;8].
Proof.
  unfold problem_163_spec.
  split.
  - intro d; split.
    + intro Hin.
      simpl in Hin.
      destruct Hin as [H2 | [H4 | [H6 | [H8 | Hnil]]]]; subst; simpl; repeat split; try lia.
      * exists 1. simpl. reflexivity.
      * exists 2. simpl. reflexivity.
      * exists 3. simpl. reflexivity.
      * exists 4. simpl. reflexivity.
    + intros H.
      destruct H as (Hmin & Hmax & Hdlt & Heven).
      destruct Heven as [k Hk].
      subst d.
      assert (1 <= k) by lia.
      assert (k <= 4) by lia.
      destruct k as [|k]; try lia.
      destruct k as [|k].
      * simpl. left. reflexivity.
      * destruct k as [|k].
        { simpl. right. left. reflexivity. }
        { destruct k as [|k].
          { simpl. right. right. left. reflexivity. }
          { destruct k as [|k].
            { simpl. right. right. right. left. reflexivity. }
            { exfalso. lia }
          }
        }
  - split.
    + (* Sorted le [2;4;6;8] *)
      apply Sorted_cons.
      * (* Forall (le 2) [4;6;8] *)
        constructor; [lia|].
        constructor; [lia|].
        constructor; [lia|constructor].
      * apply Sorted_cons.
        -- (* Forall (le 4) [6;8] *)
           constructor; [lia|].
           constructor; [lia|constructor].
        -- apply Sorted_cons.
           ++ (* Forall (le 6) [8] *)
              constructor; [lia|constructor].
           ++ apply Sorted_cons.
              ** (* Forall (le 8) [] *)
                 constructor.
              ** constructor.
    + (* NoDup [2;4;6;8] *)
      constructor.
      * intro Hin. simpl in Hin.
        destruct Hin as [H|[H|[H|[]]]]; inversion H.
      * constructor.
        -- intro Hin. simpl in Hin.
           destruct Hin as [H|[H|[]]]; inversion H.
        -- constructor.
           ++ intro Hin. simpl in Hin.
              destruct Hin as [H|[]]; inversion H.
           ++ constructor.
Qed.