Require Import List.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

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
  problem_73_spec [2%Z; 13%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 40%Z; 4%Z; 5%Z; 4%Z; 4%Z; 3%Z; 4%Z; -5%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 4%Z; 4%Z] 8%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 22 *)
  (* half_len = 11 *)
  (* first_half = firstn 11 arr = [2; 13; 3; 4; 5; 4; 3; 40; 4; 5; 4] *)
  (* second_half = skipn (22 - 11) arr = skipn 11 arr = [4; 4; 3; 4; -5; 5; 4; 3; 2; 1; 4; 4] (but length 11 means skipn 11 arr has 11 elements) Actually arr length is 22, so skipn 11 arr = last 11 elements *)
  (* skipn 11 arr = [4; 4; 3; 4; -5; 5; 4; 3; 2; 1; 4; 4] has 12 elements? Let's verify carefully *)
  (* arr length = 22 *)
  (* So skipn (22 - 11) = skipn 11 arr *)
  (* arr = [2;13;3;4;5;4;3;40;4;5;4;4;3;4;-5;5;4;3;2;1;4;4] *)
  (* Index 0-based: 0->2, ..., 10->4, 11->4 *)
  (* skipn 11 arr = drop first 11 elements: elements from index 11 to 21 (inclusive) *)
  (* Elements: indices 11 to 21: [4;3;4;-5;5;4;3;2;1;4;4] length 11 *)
  (* rev second_half = reverse of above = [4;4;1;2;3;4;5;-5;4;3;4] *)

  (* count_diff first_half and rev second_half: *)
  (* first_half = [2; 13; 3; 4; 5; 4; 3; 40; 4; 5; 4] *)
  (* rev second_half = [4;4;1;2;3;4;5;-5;4;3;4] *)
  (* Compare elements: *)
  (* 2 vs 4 -> diff 1 *)
  (* 13 vs 4 -> diff 2 *)
  (* 3 vs 1 -> diff 3 *)
  (* 4 vs 2 -> diff 4 *)
  (* 5 vs 3 -> diff 5 *)
  (* 4 vs 4 -> same 5 *)
  (* 3 vs 5 -> diff 6 *)
  (* 40 vs -5 -> diff 7 *)
  (* 4 vs 4 -> same 7 *)
  (* 5 vs 3 -> diff 8 *)
  (* 4 vs 4 -> same 8 *)

  reflexivity.
Qed.