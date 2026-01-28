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
  problem_73_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 4%Z; -7%Z; 4%Z; 5%Z; 4%Z; 4%Z; 3%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z] 2%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 17 *)
  (* half_len = 8 *)
  (* first_half = firstn 8 [1;2;3;4;5;4;-7;4;5;4;4;3;5;4;3;2;1] = [1;2;3;4;5;4;-7;4] *)
  (* second_half = skipn (17 - 8) arr = skipn 9 arr = [4;3;5;4;3;2;1] *)
  (* rev second_half = [1;2;3;4;3;5;4] *)
  (* count_diff [1;2;3;4;5;4;-7;4] [1;2;3;4;3;5;4] 0 *)
  (* Compare elements pairwise up to length of second list (7 elements): *)
  (* 1 vs 1 -> same, acc=0 *)
  (* 2 vs 2 -> same, acc=0 *)
  (* 3 vs 3 -> same, acc=0 *)
  (* 4 vs 4 -> same, acc=0 *)
  (* 5 vs 3 -> diff, acc=1 *)
  (* 4 vs 5 -> diff, acc=2 *)
  (* -7 vs 4 -> diff, acc=3 *)
  (* The 8th element of first_half (4) ignored because second list exhausted *)
  (* count_diff stops when either list is empty, count = 3 *)
  (* But definition only compares as long as both lists have elements *)
  (* So the result should be 3, but output is given as 2 here *)
  (* Let’s re-examine the code: second_half is skipn (len - half_len) arr *)
  (* len = 17, half_len = 8, len - half_len = 9 *)
  (* skipn 9 arr = drop first 9 elements from arr: *)
  (* arr = [1;2;3;4;5;4;-7;4;5;4;4;3;5;4;3;2;1] *)
  (* drop first 9: [4;4;3;5;4;3;2;1] *)
  (* rev second_half = rev [4;4;3;5;4;3;2;1] = [1;2;3;4;5;3;4;4] *)
  (* Now count_diff compares first_half = [1;2;3;4;5;4;-7;4] with rev second_half = [1;2;3;4;5;3;4;4] *)
  (* compare pairs: *)
  (* 1 vs 1 => same *)
  (* 2 vs 2 => same *)
  (* 3 vs 3 => same *)
  (* 4 vs 4 => same *)
  (* 5 vs 5 => same *)
  (* 4 vs 3 => diff (1) *)
  (* -7 vs 4 => diff (2) *)
  (* 4 vs 4 => same *)
  (* total diffs = 2 *)
  (* Result = 2 *)
  reflexivity.
Qed.