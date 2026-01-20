Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive FirstDigit : Z -> Z -> Prop :=
| fd_base : forall n, 0 <= n < 10 -> FirstDigit n n
| fd_rec : forall n d, n >= 10 -> FirstDigit (n / 10) d -> FirstDigit n d.

Definition IsOddDigit (d : Z) : Prop :=
  In d [1; 3; 5; 7; 9].

Definition SpecialCondition (n : Z) : Prop :=
  n > 10 /\
  IsOddDigit (n mod 10) /\
  exists d, FirstDigit n d /\ IsOddDigit d.

Inductive CountSpecial : list Z -> Z -> Prop :=
| cs_nil : CountSpecial [] 0
| cs_cons_true : forall x xs count,
    SpecialCondition x ->
    CountSpecial xs count ->
    CountSpecial (x :: xs) (count + 1)
| cs_cons_false : forall x xs count,
    ~ SpecialCondition x ->
    CountSpecial xs count ->
    CountSpecial (x :: xs) count.

Definition specialFilter_spec (nums : list Z) (ans : Z) : Prop :=
  CountSpecial nums ans.

Lemma not_special_5 : ~ SpecialCondition 5.
Proof.
  unfold SpecialCondition.
  intros [H _].
  lia.
Qed.

Lemma not_special_neg2 : ~ SpecialCondition (-2).
Proof.
  unfold SpecialCondition.
  intros [H _].
  lia.
Qed.

Lemma not_special_1 : ~ SpecialCondition 1.
Proof.
  unfold SpecialCondition.
  intros [H _].
  lia.
Qed.

Lemma not_special_neg5 : ~ SpecialCondition (-5).
Proof.
  unfold SpecialCondition.
  intros [H _].
  lia.
Qed.

Example specialFilter_test : specialFilter_spec [5; -2; 1; -5] 0.
Proof.
  unfold specialFilter_spec.
  apply cs_cons_false.
  - exact not_special_5.
  - apply cs_cons_false.
    + exact not_special_neg2.
    + apply cs_cons_false.
      * exact not_special_1.
      * apply cs_cons_false.
        -- exact not_special_neg5.
        -- apply cs_nil.
Qed.