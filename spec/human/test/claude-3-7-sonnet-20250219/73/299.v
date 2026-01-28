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
  problem_73_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 2%Z; 2%Z; 1%Z; 1%Z; 4%Z; -2%Z; 5%Z; 3%Z] 5%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 13 *)
  (* half_len = 13 / 2 = 6 *)
  (* first_half = firstn 6 arr = [1;2;3;4;5;2] *)
  (* second_half = skipn (13 - 6) arr = skipn 7 arr = [1;4;-2;5;3] *)
  (* rev second_half = [3;5;-2;4;1] *)
  (* count_diff [1;2;3;4;5;2] [3;5;-2;4;1] 0 *)
  (* Compare elements pairwise until shorter list ends: *)
  (* 1 vs 3 -> diff, acc=1 *)
  (* 2 vs 5 -> diff, acc=2 *)
  (* 3 vs -2 -> diff, acc=3 *)
  (* 4 vs 4 -> same, acc=3 *)
  (* 5 vs 1 -> diff, acc=4 *)
  (* 2 vs void - second list ended (only 5 elements) so stop counting *)
  (* count only when both lists have elements - so after 5 comparisons *)
  (* Result = 4 but note that since the second list is shorter, acc stays at 4 *)
  (* In fact count_diff stops when one list ends *)
  (* So count_diff = 4 *)

  (* However this contradicts output=5 - check carefully *)

  (* The second_half calculated is skipn (len - half_len) arr = skipn (13 - 6) = skipn 7 arr *)
  (* arr: positions 0-based *)
  (* 0:1; 1:2; 2:3; 3:4; 4:5; 5:2; 6:2; 7:1; 8:1; 9:4; 10:-2; 11:5; 12:3 *)
  (* skipn 7 arr: start from index 7: [1;1;4;-2;5;3] length 6 *)

  (* Rev second_half: [3;5;-2;4;1;1] *)

  (* Now first_half is length 6: [1;2;3;4;5;2] *)
  (* So count_diff compares: *)
  (* 1 vs 3 -> diff acc=1 *)
  (* 2 vs 5 -> diff acc=2 *)
  (* 3 vs -2 -> diff acc=3 *)
  (* 4 vs 4 -> same acc=3 *)
  (* 5 vs 1 -> diff acc=4 *)
  (* 2 vs 1 -> diff acc=5 *)

  (* Result 5 *)

  reflexivity.
Qed.