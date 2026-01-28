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
  (a_val i + a_val j + a_val k) mod 3 = 0.

Definition problem_147_pre (n : nat) : Prop := (n > 0)%nat.

Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  exists (l : list (nat * nat * nat)),
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\
    NoDup l /\
    output = length l.

Lemma mod_sum3 :
  forall a b c m,
    m <> 0 ->
    (a + b + c) mod m = ((a mod m) + (b mod m) + (c mod m)) mod m.
Proof.
  intros a b c m Hm.
  rewrite Z.add_assoc.
  rewrite Z.add_mod by assumption.
  rewrite Z.add_mod by assumption.
  rewrite Z.mod_mod by assumption.
  replace (c mod m) with ((c mod m) mod m) by (apply Z.mod_mod; assumption).
  rewrite <- Z.add_mod by assumption.
  rewrite <- Z.add_assoc.
  reflexivity.
Qed.

Lemma a_val_mod3_small_classify :
  forall i, (1 <= i)%nat /\ (i <= 5)%nat ->
    (a_val i mod 3 = 0 /\ (i=2 \/ i=5)) \/ (a_val i mod 3 = 1 /\ (i=1 \/ i=3 \/ i=4)).
Proof.
  intros i [Hi Hle].
  destruct i as [|i1]; [lia|].
  destruct i1 as [|i2].
  - (* i = 1 *)
    right. split; [compute|auto].
  - destruct i2 as [|i3].
    + (* i = 2 *)
      left. split; [compute|auto].
    + destruct i3 as [|i4].
      * (* i = 3 *)
        right. split; [compute|auto].
      * destruct i4 as [|i5].
        { (* i = 4 *)
          right. split; [compute|auto]. }
        destruct i5 as [|i6].
        { (* i = 5 *)
          left. split; [compute|auto]. }
        lia.
Qed.

Lemma a_val_mod3_in_0or1 :
  forall i, (1 <= i)%nat /\ (i <= 5)%nat -> (a_val i mod 3 = 0 \/ a_val i mod 3 = 1).
Proof.
  intros i Hi.
  destruct (a_val_mod3_small_classify i Hi) as [[H _] | [H _]]; [left | right]; exact H.
Qed.

Lemma bits_sum_mod3_zero_cases :
  forall r1 r2 r3 : Z,
    (r1 = 0 \/ r1 = 1) ->
    (r2 = 0 \/ r2 = 1) ->
    (r3 = 0 \/ r3 = 1) ->
    (r1 + r2 + r3) mod 3 = 0 ->
    (r1 = 0 /\ r2 = 0 /\ r3 = 0) \/ (r1 = 1 /\ r2 = 1 /\ r3 = 1).
Proof.
  intros r1 r2 r3 H1 H2 H3 Hsum.
  destruct H1 as [Hr1|Hr1]; destruct H2 as [Hr2|Hr2]; destruct H3 as [Hr3|Hr3]; subst; compute in Hsum;
    try discriminate; [left; auto|right; auto].
Qed.

Example problem_147_test_5 : problem_147_spec 5%nat 1%nat.
Proof.
  unfold problem_147_spec.
  exists [(1,3,4)].
  repeat split.
  - intros ijk Hin.
    simpl in Hin.
    destruct Hin as [H|H]; [inversion H; subst|contradiction].
    unfold is_valid_triple.
    repeat split; try lia.
    unfold a_val; simpl; compute; reflexivity.
  - intros i j k Hvalid.
    simpl.
    destruct Hvalid as [Hi [Hij [Hjk [Hkle Hsum]]]].
    assert (Hik : (i < k)%nat) by (eapply Nat.lt_trans; eauto).
    assert (Hile5 : (i <= 5)%nat) by (eapply Nat.le_trans; [apply Nat.lt_le_incl; exact Hik|exact Hkle]).
    assert (Hjle5 : (j <= 5)%nat) by (eapply Nat.le_trans; [apply Nat.lt_le_incl; exact Hjk|exact Hkle]).
    assert (Hige1 : (1 <= i)%nat) by exact Hi.
    assert (Hjge1 : (1 <= j)%nat) by lia.
    assert (Hkge1 : (1 <= k)%nat) by lia.
    set (ri := a_val i mod 3).
    set (rj := a_val j mod 3).
    set (rk := a_val k mod 3).
    assert (Hri01 : ri = 0 \/ ri = 1) by (apply a_val_mod3_in_0or1; split; assumption).
    assert (Hrj01 : rj = 0 \/ rj = 1) by (apply a_val_mod3_in_0or1; split; assumption).
    assert (Hrk01 : rk = 0 \/ rk = 1) by (apply a_val_mod3_in_0or1; split; assumption).
    assert (Hsum_res :
              (ri + rj + rk) mod 3 = 0).
    { unfold ri, rj, rk.
      rewrite <- mod_sum3 with (m:=3); [exact Hsum|lia].
    }
    destruct (bits_sum_mod3_zero_cases ri rj rk Hri01 Hrj01 Hrk01 Hsum_res)
      as [[Hri0 [Hrj0 Hrk0]] | [Hri1 [Hrj1 Hrk1]]].
    + (* All residues are 0: impossible due to strict increasing and only two indices {2,5} *)
      pose proof (a_val_mod3_small_classify i (conj Hige1 Hile5)) as Hi_class.
      pose proof (a_val_mod3_small_classify j (conj Hjge1 Hjle5)) as Hj_class.
      pose proof (a_val_mod3_small_classify k (conj Hkge1 Hkle)) as Hk_class.
      destruct Hi_class as [[Hri0' Hi_vals] | [Hri1' _]]; [|congruence].
      destruct Hj_class as [[Hrj0' Hj_vals] | [Hrj1' _]]; [|congruence].
      destruct Hk_class as [[Hrk0' Hk_vals] | [Hrk1' _]]; [|congruence].
      clear Hri0' Hrj0' Hrk0'.
      destruct Hi_vals as [Hi2|Hi5]; subst.
      * destruct Hj_vals as [Hj2|Hj5]; subst.
        -- lia.
        -- destruct Hk_vals as [Hk2|Hk5]; subst; lia.
      * lia.
    + (* All residues are 1: must be i=1, j=3, k=4 *)
      pose proof (a_val_mod3_small_classify i (conj Hige1 Hile5)) as Hi_class.
      pose proof (a_val_mod3_small_classify j (conj Hjge1 Hjle5)) as Hj_class.
      pose proof (a_val_mod3_small_classify k (conj Hkge1 Hkle)) as Hk_class.
      destruct Hi_class as [[Hri0' _] | [Hri1' Hi_vals]]; [congruence|].
      destruct Hj_class as [[Hrj0' _] | [Hrj1' Hj_vals]]; [congruence|].
      destruct Hk_class as [[Hrk0' _] | [Hrk1' Hk_vals]]; [congruence|].
      clear Hri1' Hrj1' Hrk1'.
      destruct Hi_vals as [Hi1 | [Hi3 | Hi4]]; subst.
      * (* i = 1 *)
        destruct Hj_vals as [Hj1 | [Hj3 | Hj4]]; subst.
        -- lia.
        -- (* j = 3 *)
           destruct Hk_vals as [Hk1 | [Hk3 | Hk4]]; subst; try lia.
           simpl; auto.
        -- (* j = 4 *)
           destruct Hk_vals as [Hk1 | [Hk3 | Hk4]]; subst; lia.
      * (* i = 3 *)
        destruct Hj_vals as [Hj1 | [Hj3 | Hj4]]; subst; try lia.
        destruct Hk_vals as [Hk1 | [Hk3 | Hk4]]; subst; lia.
      * (* i = 4 *)
        lia.
  - (* NoDup l *)
    simpl. constructor; [intros H; contradiction|constructor].
  - (* output length *)
    simpl. reflexivity.
Qed.