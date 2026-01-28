Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Fixpoint all_digits_odd_list (l : list nat) : Prop :=
  match l with
  | [] => True
  | h :: t => is_odd_digit h /\ all_digits_odd_list t
  end.

Fixpoint nat_to_digits_fueled (n fuel : nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      if Nat.eqb n 0 then []
      else (n mod 10) :: nat_to_digits_fueled (n / 10) fuel'
  end.

Definition nat_to_digits (n : nat) : list nat :=
  nat_to_digits_fueled n n.

Definition has_only_odd_digits (n : nat) : Prop :=
  all_digits_odd_list (nat_to_digits n).

Definition has_only_odd_digits_bool (n : nat) : bool :=
  let digits := nat_to_digits n in
  forallb (fun d => orb (Nat.eqb d 1)
                   (orb (Nat.eqb d 3)
                     (orb (Nat.eqb d 5)
                       (orb (Nat.eqb d 7)
                            (Nat.eqb d 9))))) digits.

Fixpoint filter_odd_digits (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t =>
      if has_only_odd_digits_bool h then
        h :: filter_odd_digits t
      else
        filter_odd_digits t
  end.

Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t =>
      if x <=? h then x :: l else h :: insert_sorted x t
  end.

Fixpoint sort_list (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_list t)
  end.

Definition unique_digits_impl (x : list nat) : list nat :=
  sort_list (filter_odd_digits x).

Definition problem_104_pre (x : list nat) : Prop := Forall (fun n => n > 0) x.

Definition problem_104_spec (x y : list nat) : Prop :=
  y = unique_digits_impl x.

Example test_unique_digits_1 :
  problem_104_spec [15; 33; 1422; 1] [1; 15; 33].
Proof.
  unfold problem_104_spec, unique_digits_impl.
  (* Simplify filter_odd_digits for input [15;33;1422;1] *)
  unfold filter_odd_digits, has_only_odd_digits_bool, nat_to_digits.
  simpl.

  (* nat_to_digits for 15: *)
  (* nat_to_digits_fueled 15 15 = [5;1] *)
  (* Check forallb for [5;1] *)
  (* 5 and 1 are odd digits *)
  remember (forallb (fun d => orb (Nat.eqb d 1)
                     (orb (Nat.eqb d 3)
                          (orb (Nat.eqb d 5)
                               (orb (Nat.eqb d 7)
                                    (Nat.eqb d 9))))) [5;1]) as b15.
  simpl in b15.
  rewrite Nat.eqb_refl in *.
  repeat (rewrite orb_true_r in b15 || rewrite orb_true_l in b15).
  simpl in b15.
  (* Actually compute: *)
  cbn in b15.
  unfold Nat.eqb in *.
  simpl in b15.
  (* manual: 5 -> matches Nat.eqb 5 5 = true, 1 -> Nat.eqb 1 1 = true *)
  assert (b15 = true) by reflexivity.
  subst b15.

  (* nat_to_digits for 33: [3;3] *)
  remember (forallb (fun d => orb (Nat.eqb d 1)
                     (orb (Nat.eqb d 3)
                          (orb (Nat.eqb d 5)
                               (orb (Nat.eqb d 7)
                                    (Nat.eqb d 9))))) [3;3]) as b33.
  simpl in b33.
  rewrite Nat.eqb_refl in *.
  cbn in b33.
  assert (b33 = true) by reflexivity.
  subst b33.

  (* nat_to_digits for 1422: [2;2;4;1] *)
  remember (forallb (fun d => orb (Nat.eqb d 1)
                     (orb (Nat.eqb d 3)
                          (orb (Nat.eqb d 5)
                               (orb (Nat.eqb d 7)
                                    (Nat.eqb d 9))))) [2;2;4;1]) as b1422.
  simpl in b1422.
  (* For 2, Nat.eqb 2 1 = false, 2 3 false, 2 5 false, 2 7 false, 2 9 false => false *)
  assert (b1422 = false) by reflexivity.
  subst b1422.

  (* nat_to_digits for 1: [1] *)
  remember (forallb (fun d => orb (Nat.eqb d 1)
                     (orb (Nat.eqb d 3)
                          (orb (Nat.eqb d 5)
                               (orb (Nat.eqb d 7)
                                    (Nat.eqb d 9))))) [1]) as b1.
  simpl in b1.
  rewrite Nat.eqb_refl in *.
  assert (b1 = true) by reflexivity.
  subst b1.

  (* So filter_odd_digits gives [15; 33; 1] *)
  simpl.

  (* Now sort_list [15;33;1] *)

  (* sort_list [15;33;1] = insert_sorted 15 (sort_list [33;1]) *)
  simpl.

  (* sort_list [33;1] = insert_sorted 33 (sort_list [1]) *)
  simpl.

  (* sort_list [1] = insert_sorted 1 [] = [1] *)
  simpl.

  (* insert_sorted 33 [1] *)

  unfold insert_sorted.
  simpl.
  (* 33 <=? 1 = false, so 1 :: insert_sorted 33 [] = [1;33] *)
  simpl.

  (* insert_sorted 15 [1;33] *)
  unfold insert_sorted.
  simpl.
  (* 15 <=? 1 = false, so 1 :: insert_sorted 15 [33] *)
  simpl.

  (* insert_sorted 15 [33] *)
  unfold insert_sorted.
  simpl.
  (* 15 <=? 33 = true, so 15 :: 33 :: [] = [15;33] *)
  simpl.

  (* Therefore insert_sorted 15 [1;33] = 1 :: [15;33] = [1;15;33] *)
  reflexivity.
Qed.