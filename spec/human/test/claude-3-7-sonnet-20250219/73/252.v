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
  problem_73_spec
    [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 14%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 10%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z; 2%Z; 27%Z]
    25%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 52 *)
  (* half_len = 26 *)
  (* first_half = firstn 26 arr *)
  (* = [1;2;3;4;5;6;14;7;8;9;10;11;12;13;14;15;16;10;17;18;19;20;21;22;23;24] *)
  (* second_half = skipn (52 - 26) arr = skipn 26 arr *)
  (* = [25;26;27;28;29;30;31;32;33;34;35;36;38;39;40;41;42;43;44;45;46;47;48;49;50;2;27] *)
  (* rev second_half = [27;2;50;49;48;47;46;45;44;43;42;41;40;39;38;36;35;34;33;32;31;30;29;28;27;26;25] *)
  (* count_diff first_half (rev second_half) 0 *)
  (* Compare elements pairwise: *)
  (* 1 vs 27 - different *)
  (* 2 vs 2 - same *)
  (* 3 vs 50 - different *)
  (* 4 vs 49 - different *)
  (* 5 vs 48 - different *)
  (* 6 vs 47 - different *)
  (* 14 vs 46 - different *)
  (* 7 vs 45 - different *)
  (* 8 vs 44 - different *)
  (* 9 vs 43 - different *)
  (* 10 vs 42 - different *)
  (* 11 vs 41 - different *)
  (* 12 vs 40 - different *)
  (* 13 vs 39 - different *)
  (* 14 vs 38 - different *)
  (* 15 vs 36 - different *)
  (* 16 vs 35 - different *)
  (* 10 vs 34 - different *)
  (* 17 vs 33 - different *)
  (* 18 vs 32 - different *)
  (* 19 vs 31 - different *)
  (* 20 vs 30 - different *)
  (* 21 vs 29 - different *)
  (* 22 vs 28 - different *)
  (* 23 vs 27 - different *)
  (* 24 vs 26 - different *)
  (* total differences = 25 *)
  reflexivity.
Qed.