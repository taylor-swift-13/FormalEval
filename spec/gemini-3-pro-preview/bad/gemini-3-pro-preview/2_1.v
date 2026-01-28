Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.

Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number >= 0 ->
  exists i : Z, IZR i <= number < IZR i + 1 /\ result = number - IZR i.

Example test_truncate : truncate_number_spec 3.5 0.5.
Proof.
  unfold truncate_number_spec.
  intros _.
  exists 3%Z.
  split.
  - split.
    + (* Prove 3 <= 3.5 *)
      change (IZR 3) with 3.
      apply Rmult_le_reg_r with (r := 2).
      * apply Rlt_0_2.
      * (* 3 * 2 <= 3.5 * 2 *)
        replace (3 * 2) with 6 by field.
        replace (3.5 * 2) with 7 by field.
        replace 6 with (IZR 6) by reflexivity.
        replace 7 with (IZR 7) by reflexivity.
        apply IZR_le.
        apply Z.leb_le.
        reflexivity.
    + (* Prove 3.5 < 4 *)
      replace (IZR 3 + 1) with 4 by (simpl; field).
      apply Rmult_lt_reg_r with (r := 2).
      * apply Rlt_0_2.
      * (* 3.5 * 2 < 4 * 2 *)
        replace (3.5 * 2) with 7 by field.
        replace (4 * 2) with 8 by field.
        replace 7 with (IZR 7) by reflexivity.
        replace 8 with (IZR 8) by reflexivity.
        apply IZR_lt.
        apply Z.ltb_lt.
        reflexivity.
  - (* Prove 0.5 = 3.5 - 3 *)
    change (IZR 3) with 3.
    field.
Qed.