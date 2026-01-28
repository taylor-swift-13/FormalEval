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
  problem_73_spec [26%Z; 2%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 4%Z; 5%Z; -8%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 2%Z; 30%Z] 2%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 17 *)
  (* half_len = 8 *)
  (* first_half = firstn 8 arr = [26; 2; 3; 4; 5; 4; 3; 4] *)
  (* second_half = skipn (17 - 8) arr = skipn 9 arr = [3;4;5;4;3;2;30] *)
  (* rev second_half = [30;2;3;4;5;4;3] *)
  (* count_diff compares first_half and rev second_half pairwise up to length 7 *)
  (* Compare pairs: *)
  (* 26 vs 30 -> diff, acc=1 *)
  (* 2 vs 2 -> same, acc=1 *)
  (* 3 vs 3 -> same, acc=1 *)
  (* 4 vs 4 -> same, acc=1 *)
  (* 5 vs 5 -> same, acc=1 *)
  (* 4 vs 4 -> same, acc=1 *)
  (* 3 vs 3 -> same, acc=1 *)
  (* Note first_half has length 8, second_half reversed length 7, so last element of first_half (4) ignored *)
  (* Result = 1 *)
  (* However, count_diff completes on min length so acc ends 1 *)
  (* But wait, the expected output given is 2, check if half_len calculation is correct *)

  (* length arr = 17; half_len = 8 *)
  (* first_half length = 8 *)
  (* second_half = skipn (17-8) = skipn 9 *)
  (* second_half length = 8 *)
  (* rev second_half length = 8 *)
  (* So count_diff compares 8 elements *)

  (* second_half = [3;4;5;4;3;2;30;??] *)
  (* Wait skipn 9 arr: arr: [26;2;3;4;5;4;3;4;5;-8;3;4;5;4;3;2;30] *)
  (* Indexing starts at 0: *)
  (* 0:26,1:2,2:3,3:4,4:5,5:4,6:3,7:4,8:5,9:-8,10:3,11:4,12:5,13:4,14:3,15:2,16:30 *)
  (* skipn 9 arr = elements from index 9 onwards: [-8;3;4;5;4;3;2;30] length 8 *)

  (* rev second_half = [30;2;3;4;5;4;3;-8] *)

  (* Compare 8 pairs: *)
  (* 26 vs 30 -> diff 1 *)
  (* 2 vs 2 -> same 1 *)
  (* 3 vs 3 -> same 1 *)
  (* 4 vs 4 -> same 1 *)
  (* 5 vs 5 -> same 1 *)
  (* 4 vs 4 -> same 1 *)
  (* 3 vs 3 -> same 1 *)
  (* 4 vs -8 -> diff 2 *)

  (* result = 2 *)

  reflexivity.
Qed.