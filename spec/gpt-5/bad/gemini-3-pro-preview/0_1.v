Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  let P := exists i j x y,
    Nat.lt i j /\
    nth_error numbers i = Some x /\
    nth_error numbers j = Some y /\
    Rabs (x - y) < threshold in
  (result = true <-> P) /\ (result = false <-> ~ P).

Example test_has_close_elements :
  has_close_elements_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0.3 true.
Proof.
  unfold has_close_elements_spec.
  split.
  - (* result = true <-> P *)
    split.
    + (* true = true -> P *)
      intros _.
      exists 2%nat, 3%nat, 3.9, 4.0.
      repeat split.
      * (* 2 < 3 *)
        apply Nat.lt_succ_diag_r.
      * (* nth_error numbers 2 = Some 3.9 *)
        simpl. reflexivity.
      * (* nth_error numbers 3 = Some 4.0 *)
        simpl. reflexivity.
      * (* Rabs (3.9 - 4.0) < 0.3 *)
        unfold Rabs.
        destruct (Rcase_abs (3.9 - 4.0)) as [Hlt | Hge].
        -- (* Case 3.9 - 4.0 < 0 *)
           apply Rmult_lt_reg_r with (r := 10).
           ++ apply IZR_lt. reflexivity.
           ++ replace (-(3.9 - 4.0) * 10) with 1 by field.
              replace (0.3 * 10) with 3 by field.
              apply IZR_lt. reflexivity.
        -- (* Case 3.9 - 4.0 >= 0 (Contradiction) *)
           exfalso.
           apply Rge_minus in Hge.
           apply Rge_not_lt in Hge.
           apply Hge.
           apply Rmult_lt_reg_r with (r := 10).
           ++ apply IZR_lt. reflexivity.
           ++ replace (3.9 * 10) with 39 by field.
              replace (4.0 * 10) with 40 by field.
              apply IZR_lt. reflexivity.
    + (* P -> true = true *)
      intros _. reflexivity.
  - (* result = false <-> ~ P *)
    split; intros H; discriminate.
Qed.