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
  skjkasdkd_spec [0; 81; 12; 3; 1; 21] 3.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 3.
  split.
  - unfold is_largest_prime. split.
    + simpl. tauto.
    + split.
      * unfold is_prime. split.
        -- lia.
        -- intros d Hle Hsq.
           assert (d * d >= 4).
           { apply Z.mul_le_mono_nonneg; lia. }
           lia.
      * intros y Hin Hp.
        simpl in Hin.
        destruct Hin as [H | Hin]; [subst; destruct Hp as [Hge _]; lia | ].
        destruct Hin as [H | Hin]; [subst | ].
        { destruct Hp as [_ Hp].
          specialize (Hp 3).
          assert (2 <= 3 /\ 3 * 3 <= 81) by lia.
          destruct H as [H1 H2].
          specialize (Hp H1 H2).
          vm_compute in Hp. contradiction. }
        destruct Hin as [H | Hin]; [subst | ].
        { destruct Hp as [_ Hp].
          specialize (Hp 2).
          assert (2 <= 2 /\ 2 * 2 <= 12) by lia.
          destruct H as [H1 H2].
          specialize (Hp H1 H2).
          vm_compute in Hp. contradiction. }
        destruct Hin as [H | Hin]; [subst; lia | ].
        destruct Hin as [H | Hin]; [subst; destruct Hp as [Hge _]; lia | ].
        destruct Hin as [H | Hin]; [subst | tauto].
        { destruct Hp as [_ Hp].
          specialize (Hp 3).
          assert (2 <= 3 /\ 3 * 3 <= 21) by lia.
          destruct H as [H1 H2].
          specialize (Hp H1 H2).
          vm_compute in Hp. contradiction. }
  - vm_compute. reflexivity.
Qed.