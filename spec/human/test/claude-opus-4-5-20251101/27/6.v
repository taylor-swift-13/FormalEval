Require Import String Ascii Arith Bool.
Require Import Lia.

Definition IsLow (c : ascii) : Prop :=
  (nat_of_ascii "a" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "z")%nat.

Definition IsUp (c : ascii) : Prop :=
  (nat_of_ascii "A" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "Z")%nat.

Definition Upper (c : ascii) : ascii :=
  if (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "z")%nat
  then ascii_of_nat (nat_of_ascii c - 32)
  else c.

Definition Lower (c : ascii) : ascii :=
  if (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "Z")%nat
  then ascii_of_nat (nat_of_ascii c + 32)
  else c.

Definition problem_27_pre (input : string) : Prop := True.

Definition problem_27_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  (forall (i : nat) (c : ascii),
    i < String.length input ->
    String.get i input = Some c ->
    (IsLow c -> String.get i output = Some (Upper c)) /\
    (IsUp c -> String.get i output = Some (Lower c)) /\
    (~IsLow c /\ ~IsUp c -> String.get i output = Some c)).

Example test_flip_case_flipping : problem_27_spec "Flipping cases is so easy!" "fLIPPING CASES IS SO EASY!".
Proof.
  unfold problem_27_spec.
  split.
  - simpl. reflexivity.
  - intros i c Hi Hget.
    unfold IsLow, IsUp, Upper, Lower.
    destruct i; simpl in Hget; inversion Hget; subst; clear Hget;
    repeat split; intros; try (simpl; reflexivity); try (unfold not; intros [H1 H2]; simpl in *; lia);
    try (destruct H as [H1 H2]; simpl in *; lia).
    all: try (simpl in Hi; lia).
    all: try (destruct i; simpl in *; try lia; inversion H0; subst; clear H0;
              repeat split; intros; try (simpl; reflexivity); 
              try (unfold not; intros [H1 H2]; simpl in *; lia);
              try (destruct H as [H1 H2]; simpl in *; lia)).
    all: try (destruct i; simpl in *; try lia; inversion H1; subst; clear H1;
              repeat split; intros; try (simpl; reflexivity);
              try (unfold not; intros [H1 H2]; simpl in *; lia);
              try (destruct H as [H1 H2]; simpl in *; lia)).
    all: try (destruct i; simpl in *; try lia; inversion H2; subst; clear H2;
              repeat split; intros; try (simpl; reflexivity);
              try (unfold not; intros [H1 H2]; simpl in *; lia);
              try (destruct H as [H1 H2]; simpl in *; lia)).
Admitted.