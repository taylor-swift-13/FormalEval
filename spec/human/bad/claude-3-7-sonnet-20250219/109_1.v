(* 导入列表、整数和自然数所需的基础库 *)
Require Import List ZArith Arith.
Require Import Coq.Sorting.Sorted.
Open Scope Z_scope.
Import ListNotations.

Fixpoint is_sorted_bool (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | h1 :: t =>
      match t with
      | [] => true
      | h2 :: t' => if Z.leb h1 h2 then is_sorted_bool t else false
      end
  end.

Definition right_shift (l : list Z) : list Z :=
  match rev l with
  | [] => []
  | hd :: tl => hd :: rev tl
  end.

Fixpoint n_shifts (n : nat) (l : list Z) : list Z :=
  match n with
  | 0%nat => l
  | S n' => right_shift (n_shifts n' l)
  end.

Fixpoint check_all_shifts (arr : list Z) (n : nat) : bool :=
  match n with
  | O => is_sorted_bool arr
  | S n' => orb (is_sorted_bool (n_shifts n arr)) (check_all_shifts arr n')
  end.

Definition move_one_ball_impl (arr : list Z) : bool :=
  match arr with
  | [] => true
  | _ :: _ => check_all_shifts arr (length arr)
  end.

Definition problem_109_pre (arr : list Z) : Prop := NoDup arr.

Definition problem_109_spec (arr : list Z) (result : bool) : Prop :=
  result = move_one_ball_impl arr.

(* 新版辅助引理，使用 length_rev 替代 rev_length *)
Lemma n_shifts_length_cycle :
  forall (l : list Z),
    let len := length l in
    n_shifts len l = l.
Proof.
  intros l.
  set (len := length l).
  generalize dependent l.
  induction len as [|n IH].
  - intros l Hlen.
    simpl in Hlen.
    symmetry in Hlen.
    apply length_zero_iff_nil in Hlen.
    rewrite Hlen. simpl. reflexivity.
  - intros l Hlen.
    simpl.
    unfold right_shift.
    destruct (rev l) eqn:Heqrev.
    + simpl in Hlen.
      lia.
    + (* rev l = hd :: tl *)
      apply rev_involutive in Heqrev.
      rewrite <- Heqrev.
      (* length l = S n *)
      rewrite length_rev in Hlen.
      simpl in Hlen.
      inversion Hlen as [Htl_len].
      set (l' := tl ++ [hd]).
      assert (Hlen_l' : length l' = n).
      { unfold l'. rewrite app_length. simpl. assumption. }
      specialize (IH l' Hlen_l').
      rewrite IH.
      reflexivity.
Qed.

(* 证明示例 *)
Example test_move_one_ball_example1 :
  problem_109_spec [3%Z; 4%Z; 5%Z; 1%Z; 2%Z] true.
Proof.
  unfold problem_109_spec, move_one_ball_impl.
  simpl.

  set (arr := [3%Z;4%Z;5%Z;1%Z;2%Z]).
  remember (length arr) as n eqn:Elen.
  replace n with 5 in * by reflexivity.
  clear Elen.

  unfold check_all_shifts.
  simpl.

  (* 使用 n_shifts_length_cycle : n_shifts 5 arr = arr *)
  assert (Hcycle : n_shifts 5 arr = arr) by apply n_shifts_length_cycle.
  rewrite Hcycle.

  (* 计算 is_sorted_bool arr *)
  unfold is_sorted_bool.
  simpl.
  rewrite (Z.leb_le 3 4) by lia.
  simpl.
  rewrite (Z.leb_le 4 5) by lia.
  simpl.
  rewrite (Z.leb_le 5 1) by lia.
  simpl.
  (* 为 false *)
  rewrite orb_false_r.

  (* check_all_shifts arr 4 *)
  simpl.

  (* 计算 n_shifts 4 arr *)

  (* 手动计算 n_shifts 1 arr = right_shift arr *)
  unfold right_shift.
  simpl.
  (* rev arr = [2;1;5;4;3] *)
  (* right_shift arr = 2 :: rev [1;5;4;3] = 2 :: [3;4;5;1] = [2;3;4;5;1] *)
  set (shift1 := [2;3;4;5;1]).

  (* n_shifts 2 arr = right_shift shift1 *)
  unfold right_shift.
  simpl.
  (* rev shift1 = [1;5;4;3;2] *)
  (* right_shift shift1 = 1 :: rev [5;4;3;2] = 1 :: [2;3;4;5] = [1;2;3;4;5] *)
  set (shift2 := [1;2;3;4;5]).

  (* is_sorted_bool shift2 = true *)
  assert (Hsorted_shift2 : is_sorted_bool shift2 = true).
  {
    unfold is_sorted_bool.
    simpl.
    repeat (rewrite (Z.leb_le _ _) by lia).
    simpl.
    reflexivity.
  }
  rewrite Hsorted_shift2.
  simpl.
  (* orb true _ = true *)
  reflexivity.
Qed.