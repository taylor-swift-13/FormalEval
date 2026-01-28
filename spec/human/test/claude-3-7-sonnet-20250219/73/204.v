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
  problem_73_spec
    [1%Z; 2%Z; 3%Z; 4%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 49%Z; 13%Z; 8%Z]
    25%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 52 *)
  (* half_len = 26 *)
  (* first_half = firstn 26 arr = 
     [1;2;3;4;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27] *)
  (* second_half = skipn (52 - 26) arr = skipn 26 arr =
     [27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;48;49;49;13;8] *)
  (* rev second_half = 
     [8;13;49;49;48;47;46;45;44;43;42;41;40;39;38;37;36;35;34;33;32;31;30;29;28;27] *)
  (* count_diff first_half rev_second_half 0 with elements: *)
  (* 1 vs 8   -> diff (acc=1) *)
  (* 2 vs 13  -> diff (2) *)
  (* 3 vs 49  -> diff (3) *)
  (* 4 vs 49  -> diff (4) *)
  (* 6 vs 48  -> diff (5) *)
  (* 7 vs 47  -> diff (6) *)
  (* 8 vs 46  -> diff (7) *)
  (* 9 vs 45  -> diff (8) *)
  (* 10 vs 44 -> diff (9) *)
  (* 11 vs 43 -> diff (10) *)
  (* 12 vs 42 -> diff (11) *)
  (* 13 vs 41 -> diff (12) *)
  (* 14 vs 40 -> diff (13) *)
  (* 15 vs 39 -> diff (14) *)
  (* 16 vs 38 -> diff (15) *)
  (* 17 vs 37 -> diff (16) *)
  (* 18 vs 36 -> diff (17) *)
  (* 19 vs 35 -> diff (18) *)
  (* 20 vs 34 -> diff (19) *)
  (* 21 vs 33 -> diff (20) *)
  (* 22 vs 32 -> diff (21) *)
  (* 23 vs 31 -> diff (22) *)
  (* 24 vs 30 -> diff (23) *)
  (* 25 vs 29 -> diff (24) *)
  (* 26 vs 28 -> diff (25) *)
  (* 27 vs 27 -> same *)
  (* Result = 25 *)
  reflexivity.
Qed.