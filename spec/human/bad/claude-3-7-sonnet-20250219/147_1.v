Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition a_val (i : nat) : Z :=
  let i_z := Z.of_nat i in
  i_z * i_z - i_z + 1.

Definition is_valid_triple (n i j k : nat) : Prop :=
  (1 <= i)%nat /\ (i < j)%nat /\ (j < k)%nat /\ (k <= n)%nat /\
  ((a_val i + a_val j + a_val k) mod 3 = 0).

Definition problem_147_pre (n : nat) : Prop := n > 0.

Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  exists (l : list (nat * nat * nat)),
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\
    NoDup l /\
    output = length l.

(* Lemma: a_val modulo 3 depends only on i mod 3 *)
Lemma a_val_mod3 : forall i,
  (a_val i) mod 3 =
    match (i mod 3)%nat with
    | 0 => 1
    | 1 => 1
    | 2 => 0
    | _ => 0 (* impossible case *)
    end.
Proof.
  intros i.
  unfold a_val.
  remember (Z.of_nat i mod 3) as r eqn:Hr.
  assert (Hmod: (Z.of_nat i mod 3) = Z.of_nat (i mod 3) mod 3).
  {
    rewrite <- Z.le_mod_idemp_l by lia.
    rewrite Nat2Z.inj_mod.
    reflexivity.
  }
  rewrite <- Hmod in Hr.
  destruct (i mod 3) eqn:Hrm.
  - subst r.
    rewrite Nat2Z.inj_0.
    rewrite Z.mod_0_l by lia.
    rewrite Z.mul_0_l, Z.mul_0_r, Z.add_0_r, Z.sub_0_l.
    rewrite Z.mod_small; lia.
  - subst r.
    rewrite Nat2Z.inj_1.
    rewrite Z.mod_small by lia.
    simpl.
    ring_simplify.
    replace ((1*1 - 1 + 1) mod 3) with 1 by lia.
    reflexivity.
  - subst r.
    rewrite Nat2Z.inj_2.
    (* 2*2 - 2 + 1 = 3 *)
    replace ((2*2 - 2 + 1) mod 3) with 0 by lia.
    reflexivity.
  - lia.
Qed.

Example problem_147_test :
  problem_147_spec 5 1.
Proof.
  unfold problem_147_spec.
  (* All triples with 1 <= i < j < k <= 5 *)
  set (all_triples := [
    (1,2,3); (1,2,4); (1,2,5);
    (1,3,4); (1,3,5);
    (1,4,5);
    (2,3,4); (2,3,5);
    (2,4,5);
    (3,4,5)
  ]).
  
  (* Claim only (1,3,4) is valid *)
  set (valid := (1,3,4)).
  exists [valid].
  split.
  - intros ijk Hin.
    simpl in Hin.
    destruct Hin as [Heq|Hnil].
    + subst ijk.
      unfold is_valid_triple.
      repeat split; lia.
      (* Prove sum mod 3 = 0 for (1,3,4) *)
      unfold a_val.
      rewrite !Nat2Z.id.
      simpl.
      (* 1*1 - 1 + 1 = 1 *)
      (* 3*3 - 3 + 1 = 9 - 3 + 1 = 7 *)
      (* 4*4 - 4 + 1 = 16 - 4 + 1 = 13 *)
      replace (1 + 7 + 13) with 21 by lia.
      rewrite Z.mod_mod by lia.
      simpl.
      reflexivity.
    + contradiction.
  - split.
    + intros i j k Hvalid.
      unfold is_valid_triple in Hvalid.
      destruct Hvalid as [Hi [Hj [Hk [Hn Hmod]]]].
      (* Check that if valid triple, then (i,j,k) = (1,3,4) *)
      assert (exists eq_dec : (nat * nat * nat) -> (nat * nat * nat) -> bool,
                forall x y, if eq_dec x y then x = y else x <> y).
      { apply eq_dec_spec. }
      (* Instead, enumerate and check sums for all triples in all_triples except (1,3,4) *)
      assert (Hother : ~ In (i,j,k) [valid]).
      { intro Hin.
        destruct Hin as [Heq|Hnil].
        - subst; reflexivity.
        - contradiction.
      }
      (* Because i<j<k<=5, (i,j,k) ∈ all_triples *)
      assert (Hin_all : In (i,j,k) all_triples).
      {
        (* By definition of is_valid_triple indices *)
        pose proof (Nat.lt_le_trans i j (k)) as Hlt.
        pose proof (Nat.lt_le_trans j k 6) as Hlt2.
        clear Hmod Hi Hj Hk Hn.
        (* Enumerate all triples i<j<k<=5 *)
        lia.
      }
      (* We check (i,j,k) ≠ (1,3,4) and (i,j,k) ∈ all_triples implies sum mod3 ≠ 0 *)
      (* We proceed by case analysis on (i,j,k) in all_triples *)
      destruct i,j,k; try lia.
      all: try (
        match goal with
        | |- _ => (* compute sum and test mod 3 *)
          unfold a_val in Hmod; simpl in Hmod;
          rewrite !Nat2Z.id in *;
          simpl in *;
          let s := eval compute in (Z.of_nat i * Z.of_nat i - Z.of_nat i + 1 +
                                   Z.of_nat j * Z.of_nat j - Z.of_nat j + 1 +
                                   Z.of_nat k * Z.of_nat k - Z.of_nat k + 1) in
          assert (sum := s);
          (* compute sum mod 3 *)
          let modval := eval compute in (s mod 3) in
          assert (sum_mod := modval);
          (* Now check sum_mod = 0 fails *)
          destruct ((i,j,k) = valid) eqn:Heqvk;
          try (exfalso; apply Hother; simpl; assumption);
          try (lia);
          try (simpl in Hmod; rewrite Hmod in *; discriminate)
        end).
Qed.