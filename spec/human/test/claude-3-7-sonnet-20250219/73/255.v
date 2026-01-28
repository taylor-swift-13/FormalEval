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
    [-10%Z; -9%Z; -8%Z; -7%Z; -6%Z; -5%Z; 17%Z; -6%Z; -4%Z; -3%Z; -2%Z; -1%Z; 0%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; -7%Z; 9%Z; 10%Z; 10%Z; -5%Z; 6%Z]
    13%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 27 *)
  (* half_len = 13 *)
  (* first_half = firstn 13 arr = [-10; -9; -8; -7; -6; -5; 17; -6; -4; -3; -2; -1; 0] *)
  (* second_half = skipn (27 - 13) arr = skipn 14 arr = [1; 2; 3; 4; 5; 6; 7; 8; -7; 9; 10; 10; -5; 6] (length 13) *)
  (* actually second_half should be length 13, but this list is length 14 *)
  (* fix: second_half = skipn (27 - 13) = skipn 14 arr *)
  (* skipn 14 arr = arr from index 14: *)
  (* index base 0: arr[14] = 1 *)
  (* second_half = [1; 2; 3; 4; 5; 6; 7; 8; -7; 9; 10; 10; -5; 6] *)
  (* This is length 14, but half_len=13, so the code uses skipn (len - half_len) *)
  (* We use half_len=13, length=27, so skipn (27 - 13)= skipn 14 *)
  (* first_half length = 13, second_half length=14 *)
  (* but smallest_change_impl uses count_diff first_half (rev second_half) 0 *)
  (* so first_half shorter; count_diff will stop when first list ends *)
  (* rev second_half = [6; -5; 10; 10; 9; -7; 8; 7; 6; 5; 4; 3; 2; 1] *)
  
  (* count_diff [-10; -9; -8; -7; -6; -5; 17; -6; -4; -3; -2; -1; 0]
       [6; -5; 10; 10; 9; -7; 8; 7; 6; 5; 4; 3; 2; 1] 0*)
  (* Compare pairs up to length first_half = 13 *)
  (* -10 vs 6  different -> acc=1 *)
  (* -9 vs -5  different -> acc=2 *)
  (* -8 vs 10  different -> acc=3 *)
  (* -7 vs 10  different -> acc=4 *)
  (* -6 vs 9   different -> acc=5 *)
  (* -5 vs -7  different -> acc=6 *)
  (* 17 vs 8   different -> acc=7 *)
  (* -6 vs 7   different -> acc=8 *)
  (* -4 vs 6   different -> acc=9 *)
  (* -3 vs 5   different -> acc=10 *)
  (* -2 vs 4   different -> acc=11 *)
  (* -1 vs 3   different -> acc=12 *)
  (* 0 vs 2    different -> acc=13 *)
  (* count_diff completes with acc = 13 *)
  reflexivity.
Qed.