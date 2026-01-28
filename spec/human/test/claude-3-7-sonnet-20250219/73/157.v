Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

(*
  count_diff l1 l2 acc := 计算 l1 和 l2 之间不同元素的数量
*)
Fixpoint count_diff (l1 l2: list Z) (acc: Z): Z :=
  match l1, l2 with
  | [], _ => acc
  | _, [] => acc
  | h1 :: t1, h2 :: t2 =>
    if Z.eqb h1 h2 then
      count_diff t1 t2 acc
    else
      count_diff t1 t2 (Z.succ acc)
  end.

Definition smallest_change_impl (arr: list Z): Z :=
  let len := length arr in
  let half_len := (len / 2)%nat in
  let first_half := firstn half_len arr in
  let second_half := skipn (len - half_len) arr in
  count_diff first_half (rev second_half) 0.

Definition problem_73_pre (arr : list Z) : Prop := True.

Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  n = smallest_change_impl arr.

Example test_smallest_change_1 :
  problem_73_spec [1%Z; 2%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 12%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z] 3%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 15 *)
  (* half_len = 15 / 2 = 7 *)
  (* first_half = firstn 7 arr = [1; 2; 1; 1; 1; 2; 2] *)
  (* second_half = skipn (15 - 7) arr = skipn 8 arr = [2; 1; 1; 1; 1; 2] *)
  (* rev second_half = [2; 1; 1; 1; 1; 2] reversed = [2; 1; 1; 1; 1; 2], length 6 *)
  (* Actually since second_half length is 7 (from length-7), let's re-check *)
  (* length arr = 15 *)
  (* half_len = 7 *)
  (* skipn (15 - 7) arr = skipn 8 arr *)
  (* arr = [1;2;1;1;1;2;2;2;12;2;1;1;1;1;2] *)
  (* skipn 8 arr = [2;12;2;1;1;1;1;2] *)
  (* length of second_half = 8 *)
  (* Rev second_half = [2;1;1;1;1;2;12;2] *)
  (* first_half length = 7 *)
  (* So, count_diff first 7 elements and first 7 elements of the reversed second_half *)
  (* We must compare only 7 elements, so count_diff will stop after first list ends *)
  (* first_half = [1;2;1;1;1;2;2] *)
  (* reversed second_half = [2;1;1;1;1;2;12;2] *)
  (* Taking first 7 elements: [2;1;1;1;1;2;12] *)
  (* Compare element-wise: *)
  (* 1 vs 2 -> diff *)
  (* 2 vs 1 -> diff *)
  (* 1 vs 1 -> same *)
  (* 1 vs 1 -> same *)
  (* 1 vs 1 -> same *)
  (* 2 vs 2 -> same *)
  (* 2 vs 12 -> diff *)
  (* total differences = 3 *)
  reflexivity.
Qed.