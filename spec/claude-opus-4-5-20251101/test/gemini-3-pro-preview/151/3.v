Require Import ZArith.
Require Import List.
Require Import Reals.
Require Import Psatz.
Open Scope Z_scope.

Definition is_positive_odd_integer_prop (r : R) (n : Z) : Prop :=
  IZR n = r /\ (n > 0) /\ (n mod 2 = 1).

Inductive sum_squares_spec_rel : list R -> Z -> Prop :=
| sum_nil : sum_squares_spec_rel nil 0
| sum_cons_valid : forall r rs n s,
    is_positive_odd_integer_prop r n ->
    sum_squares_spec_rel rs s ->
    sum_squares_spec_rel (r :: rs) (n * n + s)
| sum_cons_invalid : forall r rs s,
    (forall n, ~ is_positive_odd_integer_prop r n) ->
    sum_squares_spec_rel rs s ->
    sum_squares_spec_rel (r :: rs) s.

Definition double_the_difference_spec (lst : list R) (result : Z) : Prop :=
  sum_squares_spec_rel lst result.

Example test_case_1 : double_the_difference_spec (0.1%R :: 0.2%R :: 0.3%R :: nil) 0.
Proof.
  unfold double_the_difference_spec.
  apply sum_cons_invalid.
  - intros n [H_eq _].
    apply (f_equal (fun x => x * 10)%R) in H_eq.
    replace (0.1 * 10)%R with 1%R in H_eq by lra.
    replace 10%R with (IZR 10) in H_eq by lra.
    replace 1%R with (IZR 1) in H_eq by lra.
    rewrite <- mult_IZR in H_eq.
    apply eq_IZR in H_eq.
    lia.
  - apply sum_cons_invalid.
    + intros n [H_eq _].
      apply (f_equal (fun x => x * 10)%R) in H_eq.
      replace (0.2 * 10)%R with 2%R in H_eq by lra.
      replace 10%R with (IZR 10) in H_eq by lra.
      replace 2%R with (IZR 2) in H_eq by lra.
      rewrite <- mult_IZR in H_eq.
      apply eq_IZR in H_eq.
      lia.
    + apply sum_cons_invalid.
      * intros n [H_eq _].
        apply (f_equal (fun x => x * 10)%R) in H_eq.
        replace (0.3 * 10)%R with 3%R in H_eq by lra.
        replace 10%R with (IZR 10) in H_eq by lra.
        replace 3%R with (IZR 3) in H_eq by lra.
        rewrite <- mult_IZR in H_eq.
        apply eq_IZR in H_eq.
        lia.
      * apply sum_nil.
Qed.