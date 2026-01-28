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
  problem_73_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 0%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 21%Z; 22%Z; 23%Z; 24%Z; 25%Z; 26%Z; 27%Z; 28%Z; 29%Z; 30%Z; 31%Z; 32%Z; 33%Z; 34%Z; 35%Z; 36%Z; 37%Z; 38%Z; 39%Z; 40%Z; 41%Z; 42%Z; 43%Z; 44%Z; 45%Z; 46%Z; 47%Z; 48%Z; 49%Z; 50%Z] 25%Z.
Proof.
  unfold problem_73_spec, smallest_change_impl.
  simpl.
  (* length arr = 50 *)
  (* half_len = 25 *)
  (* first_half = firstn 25 arr = [1;2;3;4;5;6;7;8;9;10;0;11;12;13;14;15;16;17;18;19;20;21;22;23;24] *)
  (* second_half = skipn (50 - 25) arr = skipn 25 arr = [25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;48;49;50] *)
  (* But since length is 50, skipn (50-25) = skipn 25 *)
  (* Actually second_half = [25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;48;49;50] (26 elements) *)
  (* However, we defined second_half := skipn (len - half_len) arr, so skipn 25 arr *)
  (* first_half length is 25, second_half length is 25 as well since arr has 50 elements *)
  (* So second_half is elements from index 25 to 49 : [25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;48;49;50] but actually it is 25 elements, 25 to 49 inclusive *)
  (* Wait 25 to 49 is 25 elements: elements at position 25..49 (0-based) *)
  (* Indexing arr from 0: positions 0..49 *)
  (* first_half: first 25 elements: positions 0..24 *)
  (* second_half: skipn (50-25)=skipn 25: elements at positions 25..49, total 25 elements *)
  (* rev second_half reverses these last 25 elements *)
  (* count_diff sums differences between first_half and rev second_half *)
  (* We compare first_half = [1..24 elements], rev second_half = reverse of [25..49] = [50;49;48;...;25] *)
  (* So compare 1 vs 50 => diff, 2 vs 49 => diff, ..., 24 vs 27 => diff, 25 vs 26 => diff? Wait first_half last element is 25th element: 24th index is 24 *)
  (* first_half last element is 24th element = arr[24] = 24 *)
  (* rev second_half first element is arr[49] = 50 *)
  (* So all are different *)
  (* So total differences = 25 *)
  reflexivity.
Qed.