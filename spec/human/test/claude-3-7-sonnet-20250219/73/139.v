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
  problem_73_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 2%Z; 30%Z] 1%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 17 *)
  (* half_len = 8 *)
  (* first_half = firstn 8 arr = [1;2;3;4;5;4;3;4] *)
  (* second_half = skipn (17 - 8) arr = skipn 9 arr = [4;3;4;5;4;3;2;30] *)
  (* rev second_half = [30;2;3;4;5;4;3;4] *)
  (* count_diff [1;2;3;4;5;4;3;4] [30;2;3;4;5;4;3;4] 0 *)
  (* Compare pairs: *)
  (* 1 vs 30 -> diff -> acc=1 *)
  (* 2 vs 2 -> same -> acc=1 *)
  (* 3 vs 3 -> same -> acc=1 *)
  (* 4 vs 4 -> same -> acc=1 *)
  (* 5 vs 5 -> same -> acc=1 *)
  (* 4 vs 4 -> same -> acc=1 *)
  (* 3 vs 3 -> same -> acc=1 *)
  (* 4 vs 4 -> same -> acc=1 *)
  reflexivity.
Qed.