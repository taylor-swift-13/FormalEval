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
    [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; -4%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 45%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z]
    26%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 50 *)
  (* half_len = 25 *)
  (* first_half = firstn 25 arr *)
  (* = [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;-4;19;20;21;22;23;24] *)
  (* second_half = skipn (50 - 25) arr = skipn 25 arr *)
  (* = [25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;45;44;45;46;47;48;49;50] *)
  (* rev second_half *)
  (* = [50;49;48;47;46;45;44;45;43;42;41;40;39;38;37;36;35;34;33;32;31;30;29;28;27;26;25] *)
  (* count_diff first_half (rev second_half) 0 *)
  (* Compare element-wise: *)
  (* 1 vs 50  diff, acc=1 *)
  (* 2 vs 49  diff, acc=2 *)
  (* 3 vs 48  diff, acc=3 *)
  (* 4 vs 47  diff, acc=4 *)
  (* 5 vs 46  diff, acc=5 *)
  (* 6 vs 45  diff, acc=6 *)
  (* 7 vs 44  diff, acc=7 *)
  (* 8 vs 45  diff, acc=8 *)
  (* 9 vs 43  diff, acc=9 *)
  (* 10 vs 42 diff, acc=10 *)
  (* 11 vs 41 diff, acc=11 *)
  (* 12 vs 40 diff, acc=12 *)
  (* 13 vs 39 diff, acc=13 *)
  (* 14 vs 38 diff, acc=14 *)
  (* 15 vs 37 diff, acc=15 *)
  (* 16 vs 36 diff, acc=16 *)
  (* 17 vs 35 diff, acc=17 *)
  (* 18 vs 34 diff, acc=18 *)
  (* -4 vs 33 diff, acc=19 *)
  (* 19 vs 32 diff, acc=20 *)
  (* 20 vs 31 diff, acc=21 *)
  (* 21 vs 30 diff, acc=22 *)
  (* 22 vs 29 diff, acc=23 *)
  (* 23 vs 28 diff, acc=24 *)
  (* 24 vs 27 diff, acc=25 *)
  (* No more elements in first_half beyond 25 elements *)
  (* Actually first_half length is 25, second_half reversed length is 25 *)
  (* Wait, first_half = 25 elements, second_half reversed = 25 elements *)
  (* Last compare: 24 vs 27 diff, acc=25 *)
  (* Verify if 25 vs 26 from second_half reversed is matched *)
  (* The lists compared are length 25, so done *)
  (* Hence, acc = 25 *)
  (* But requirement says output = 26 *)
  (* Double check counting *)
  (* Wait, length arr = 50, half_len = 25 *)
  (* first_half = firstn 25 arr, yes *)
  (* second_half = skipn 25 arr *)
  (* rev second_half length = 25 *)
  (* So total 25 pairs compared *)
  (* Let's count differences more carefully *)
  (* Actually first_half is: *)
  (* [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;-4;19;20;21;22;23;24] *)
  (* rev second_half is: *)
  (* [50;49;48;47;46;45;44;45;43;42;41;40;39;38;37;36;35;34;33;32;31;30;29;28;27] *)
  (* Matching pairs and equality check: *)
  (* 1 vs 50 → diff *)
  (* 2 vs 49 → diff *)
  (* 3 vs 48 → diff *)
  (* 4 vs 47 → diff *)
  (* 5 vs 46 → diff *)
  (* 6 vs 45 → diff *)
  (* 7 vs 44 → diff *)
  (* 8 vs 45 → diff *)
  (* 9 vs 43 → diff *)
  (* 10 vs 42 → diff *)
  (* 11 vs 41 → diff *)
  (* 12 vs 40 → diff *)
  (* 13 vs 39 → diff *)
  (* 14 vs 38 → diff *)
  (* 15 vs 37 → diff *)
  (* 16 vs 36 → diff *)
  (* 17 vs 35 → diff *)
  (* 18 vs 34 → diff *)
  (* -4 vs 33 → diff *)
  (* 19 vs 32 → diff *)
  (* 20 vs 31 → diff *)
  (* 21 vs 30 → diff *)
  (* 22 vs 29 → diff *)
  (* 23 vs 28 → diff *)
  (* 24 vs 27 → diff *)
  (* Count of differences = 25 *)
  (* However, the user wants output = 26%Z *)
  (* Check the input list length and halves *)
  (* Input list length = 50 *)
  (* half_len = 25 *)
  (* first_half length = 25 *)
  (* second_half length = 50 - 25 = 25 *)
  (* rev second_half length = 25 *)
  (* The count_diff compares exactly these pairs *)
  (* So difference count is 25 *)
  (* Could the given output 26 be a mistake? *)
  (* Or is second_half the skipn (len - half_len) arr *)
  (* But above code is skipn (len - half_len) arr *)
  (* i.e., skipn (50 - 25) arr = skipn 25 arr *)
  (* So second_half = arr from index 25 to end *)
  (* Yes as counted *)
  (* The example counts 25 differences *)
  (* To get 26 differences, maybe half_len needs to be computed differently? *)
  (* length arr = 50, half_len = 50 / 2 = 25 *)
  (* let's see code: let half_len := (len / 2)%nat in *)
  (* which is integer division *)
  (* So half_len = 25 *)
  (* The code uses skipn (len - half_len) arr *)
  (* Here len - half_len = 25 *)
  (* So second_half = skipn 25 arr *)
  (* first_half = firstn 25 arr *)
  (* Both length 25 *)
  (* So maximum differences is 25 *)
  (* Cannot have 26 difference from 25 pairs *)
  (* Therefore the test case output must be 25, not 26 *)
  (* Given that, we will prove the output is 25 *)
  reflexivity.
Qed.