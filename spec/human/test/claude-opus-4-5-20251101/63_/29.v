Require Import Coq.Init.Nat.

Inductive is_fibfib : nat -> nat -> Prop :=
  | ff_zero : is_fibfib 0 0
  | ff_one  : is_fibfib 1 0
  | ff_two  : is_fibfib 2 1
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

Lemma fibfib_3 : is_fibfib 3 1.
Proof. apply (ff_step 0 0 0 1 ff_zero ff_one ff_two). Qed.

Lemma fibfib_4 : is_fibfib 4 2.
Proof. apply (ff_step 1 0 1 1 ff_one ff_two fibfib_3). Qed.

Lemma fibfib_5 : is_fibfib 5 4.
Proof. apply (ff_step 2 1 1 2 ff_two fibfib_3 fibfib_4). Qed.

Lemma fibfib_6 : is_fibfib 6 7.
Proof. apply (ff_step 3 1 2 4 fibfib_3 fibfib_4 fibfib_5). Qed.

Lemma fibfib_7 : is_fibfib 7 13.
Proof. apply (ff_step 4 2 4 7 fibfib_4 fibfib_5 fibfib_6). Qed.

Lemma fibfib_8 : is_fibfib 8 24.
Proof. apply (ff_step 5 4 7 13 fibfib_5 fibfib_6 fibfib_7). Qed.

Lemma fibfib_9 : is_fibfib 9 44.
Proof. apply (ff_step 6 7 13 24 fibfib_6 fibfib_7 fibfib_8). Qed.

Lemma fibfib_10 : is_fibfib 10 81.
Proof. apply (ff_step 7 13 24 44 fibfib_7 fibfib_8 fibfib_9). Qed.

Lemma fibfib_11 : is_fibfib 11 149.
Proof. apply (ff_step 8 24 44 81 fibfib_8 fibfib_9 fibfib_10). Qed.

Lemma fibfib_12 : is_fibfib 12 274.
Proof. apply (ff_step 9 44 81 149 fibfib_9 fibfib_10 fibfib_11). Qed.

Lemma fibfib_13 : is_fibfib 13 504.
Proof. apply (ff_step 10 81 149 274 fibfib_10 fibfib_11 fibfib_12). Qed.

Lemma fibfib_14 : is_fibfib 14 927.
Proof. apply (ff_step 11 149 274 504 fibfib_11 fibfib_12 fibfib_13). Qed.

Lemma fibfib_15 : is_fibfib 15 1705.
Proof. apply (ff_step 12 274 504 927 fibfib_12 fibfib_13 fibfib_14). Qed.

Lemma fibfib_16 : is_fibfib 16 3136.
Proof. apply (ff_step 13 504 927 1705 fibfib_13 fibfib_14 fibfib_15). Qed.

Example test_fibfib_16 : problem_63_spec 16 3136.
Proof.
  unfold problem_63_spec.
  apply fibfib_16.
Qed.