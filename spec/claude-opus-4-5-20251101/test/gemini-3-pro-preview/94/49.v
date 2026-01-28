Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition sum_of_digits (n : Z) : Z :=
  let fix aux (m : Z) (acc : Z) (fuel : nat) :=
    match fuel with
    | O => acc
    | S fuel' =>
      if m <=? 0 then acc
      else aux (m / 10) (acc + (m mod 10)) fuel'
    end
  in aux n 0 100%nat.

Definition is_largest_prime (x : Z) (lst : list Z) : Prop :=
  In x lst /\ is_prime x /\ forall y : Z, In y lst -> is_prime y -> y <= x.

Definition skjkasdkd_spec (lst : list Z) (result : Z) : Prop :=
  (exists x : Z, is_largest_prime x lst /\ result = sum_of_digits x) \/
  ((forall x : Z, In x lst -> ~ is_prime x) /\ result = 0).

Example test_case : 
  skjkasdkd_spec [17; 1; 2; 3; 4; 5; 127; 7; 7; 8; 9; 3] 10.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 127.
  split.
  - unfold is_largest_prime. split.
    + simpl. tauto.
    + split.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hle Hsq.
           assert (d < 12).
           { destruct (Z_le_gt_dec 12 d).
             - assert (12 * 12 <= d * d) by (apply Z.mul_le_mono_nonneg; lia).
               lia.
             - lia. }
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ 
                   d = 8 \/ d = 9 \/ d = 10 \/ d = 11) by lia.
           repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           end; subst; vm_compute; discriminate.
      * intros y Hin Hp.
        simpl in Hin.
        repeat destruct Hin as [Hin | Hin]; subst; try lia.
  - vm_compute. reflexivity.
Qed.