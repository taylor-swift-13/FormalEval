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
    [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 15%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 12%Z]
    10%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 21 *)
  (* half_len = 10 *)
  (* first_half = firstn 10 arr = [1;2;3;4;5;6;7;8;9;10] *)
  (* second_half = skipn (21 - 10) arr = skipn 11 arr = [12;15;15;16;17;18;19;20;12] *)
  (* rev second_half = [12;20;19;18;17;16;15;15;12] *)
  (* count_diff first_half rev(second_half) 0 *)
  (* Compare elements: *)
  (* 1 vs 12 -> diff *)
  (* 2 vs 20 -> diff *)
  (* 3 vs 19 -> diff *)
  (* 4 vs 18 -> diff *)
  (* 5 vs 17 -> diff *)
  (* 6 vs 16 -> diff *)
  (* 7 vs 15 -> diff *)
  (* 8 vs 15 -> diff *)
  (* 9 vs 12 -> diff *)
  (* 10 vs ? -> second_half length 9, so last element of first_half not compared? *)
  (* Actually first_half length 10 vs second_half reversed length 9 *)
  (* count_diff defined on lists: stops when either empty *)
  (* So only first 9 elements compared *)
  (* Differences counted = 9 *)
  (* But demand output = 10, implies 10 differences counted *)
  (* Check lengths more carefully *)
  (* half_len = 10 *)
  (* first_half length = 10 *)
  (* second_half length = 21 - 11 = 10 *)
  (* corrected calculation: skipn (len - half_len) arr = skipn (21 - 10) arr = skipn 11 arr *)
  (* elements from index 11 onwards: arr[11..] = 12;13;15;15;16;17;18;19;20;12 ? *)
  (* Check the input carefully *)
  (* input arr: 1;2;3;4;5;6;7;8;9;10;11;12;13;15;15;16;17;18;19;20;12 *)
  (* Indices from 0 to 20 *)
  (* skipn 11 arr skips first 11 elements: elements are from index 11 *)
  (* arr[11] = 12, arr[12] = 13, arr[13] = 15, arr[14] = 15, arr[15] = 16, arr[16] = 17, arr[17] = 18, arr[18] = 19, arr[19] = 20, arr[20] = 12 *)
  (* So second_half = [12;13;15;15;16;17;18;19;20;12] length 10 *)
  (* rev second_half = [12;20;19;18;17;16;15;15;13;12] *)
  (* first_half = first 10 elements: arr[0..9] = [1;2;3;4;5;6;7;8;9;10] *)
  (* Compare elements pairwise: *)
  (* 1 vs 12 diff 1 *)
  (* 2 vs 20 diff 2 *)
  (* 3 vs 19 diff 3 *)
  (* 4 vs 18 diff 4 *)
  (* 5 vs 17 diff 5 *)
  (* 6 vs 16 diff 6 *)
  (* 7 vs 15 diff 7 *)
  (* 8 vs 15 diff 8 *)
  (* 9 vs 13 diff 9 *)
  (* 10 vs 12 diff 10 *)
  reflexivity.
Qed.