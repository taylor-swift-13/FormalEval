Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.  (* Added import for lia *)
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

Definition problem_122_pre (arr : list Z) (k : nat) : Prop :=
  (length arr >= 1)%nat /\ (length arr <= 100)%nat /\ (1 <= k)%nat /\ (k <= length arr)%nat.

Definition problem_122_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Example test_case_1 :
  problem_122_spec [1%Z; -2%Z; -3%Z; 41%Z; 57%Z; 76%Z; 87%Z; 88%Z; 99%Z] 3%nat (-4%Z).
Proof.
  unfold problem_122_spec.
  simpl.
  (* firstn 3 [...] = [1; -2; -3] *)
  (* show is_at_most_two_digits returns true on these elements *)
  assert (H1: is_at_most_two_digits 1 = true).
  { unfold is_at_most_two_digits.
    rewrite !Z.ltb_lt.
    lia.
  }
  assert (H2: is_at_most_two_digits (-2) = true).
  { unfold is_at_most_two_digits.
    rewrite !Z.ltb_lt.
    lia.
  }
  assert (H3: is_at_most_two_digits (-3) = true).
  { unfold is_at_most_two_digits.
    rewrite !Z.ltb_lt.
    lia.
  }
  rewrite H1, H2, H3.
  simpl.
  reflexivity.
Qed.