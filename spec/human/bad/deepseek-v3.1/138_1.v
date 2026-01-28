Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition problem_138_pre (n : Z) : Prop := True.

Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Example test_case_4 : problem_138_spec 4 false.
Proof.
  unfold problem_138_spec.
  split.
  - intros H. discriminate H.  (* false = true -> False *)
  - intros Hcontra.
    destruct Hcontra as (e1 & e2 & e3 & e4 & H1 & H2 & H3 & H4 & Hsum).
    unfold is_positive_even in H1, H2, H3, H4.
    destruct H1 as (k1 & He1 & Hk1).
    destruct H2 as (k2 & He2 & Hk2).
    destruct H3 as (k3 & He3 & Hk3).
    destruct H4 as (k4 & He4 & Hk4).
    rewrite He1, He2, He3, He4 in Hsum.
    assert (Htotal : 4 = 2 * (k1 + k2 + k3 + k4)) by lia.
    assert (Hk_sum : k1 + k2 + k3 + k4 = 2) by lia.
    assert (Hmin_sum : k1 + k2 + k3 + k4 >= 4).
    { apply Z.add_le_mono; [apply Z.add_le_mono; [apply Z.add_le_mono|]|];
      try apply Z.lt_le_incl; assumption. }
    lia.
Qed.