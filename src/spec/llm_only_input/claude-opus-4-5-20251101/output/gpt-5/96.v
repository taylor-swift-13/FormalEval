Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Lia.

Import ListNotations.

Definition divides (d n : nat) : Prop :=
  exists k, n = Nat.mul d k.

Definition prime (p : nat) : Prop :=
  2 <= p /\ forall d, 2 <= d /\ d < p -> ~ divides d p.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  NoDup ans /\
  forall p, In p ans <-> prime p /\ p < n.

Lemma prime_2 : prime 2.
Proof.
  unfold prime. split.
  - lia.
  - intros d [H1 H2]. lia.
Qed.

Lemma prime_3 : prime 3.
Proof.
  unfold prime. split.
  - lia.
  - intros d [H1 H2].
    unfold divides. intros [k Hk].
    destruct d.
    + lia.
    + destruct d.
      * lia.
      * destruct d.
        -- simpl in Hk. lia.
        -- lia.
Qed.

Lemma two_three_nodup : NoDup [2; 3].
Proof.
  constructor.
  - simpl. intros [H | H].
    + discriminate.
    + exact H.
  - constructor.
    + simpl. intros [].
    + constructor.
Qed.

Example count_up_to_5 : count_up_to_spec 5 [2; 3].
Proof.
  unfold count_up_to_spec.
  split.
  - exact two_three_nodup.
  - intros p. split.
    + intros Hin. simpl in Hin.
      destruct Hin as [H | [H | F]].
      * subst p. split. exact prime_2. lia.
      * subst p. split. exact prime_3. lia.
      * contradiction.
    + intros [Hprime Hlt].
      unfold prime in Hprime.
      destruct Hprime as [Hge2 Hdiv].
      simpl.
      assert (p = 2 \/ p = 3 \/ p = 4) as Hcases by lia.
      destruct Hcases as [H2 | [H3 | H4]].
      * left. symmetry. exact H2.
      * right. left. symmetry. exact H3.
      * exfalso. subst p.
        specialize (Hdiv 2).
        assert (Hcond : 2 <= 2 /\ 2 < 4) by lia.
        specialize (Hdiv Hcond).
        apply Hdiv.
        unfold divides. exists 2. reflexivity.
Qed.