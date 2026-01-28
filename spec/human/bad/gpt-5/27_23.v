Require Import String Ascii Arith Bool Lia.

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

Example problem_27_example_fun : problem_27_spec "Fun" "fUN".
Proof.
  unfold problem_27_spec.
  simpl.
  split.
  - reflexivity.
  - intros i c Hlt Hget.
    destruct i as [| i].
    + simpl in Hget. inversion Hget; subst c.
      repeat split.
      * intros [H1 H2]. simpl in H1, H2. lia.
      * intros _. simpl. reflexivity.
      * intros [HnL HnU]. exfalso. apply HnU. split; simpl; lia.
    + destruct i as [| i].
      * simpl in Hget. inversion Hget; subst c.
        repeat split.
        - intros _. simpl. reflexivity.
        - intros [H1 H2]. simpl in H1, H2. lia.
        - intros [HnL HnU]. exfalso. apply HnL. split; simpl; lia.
      * destruct i as [| i].
        -- simpl in Hget. inversion Hget; subst c.
           repeat split.
           + intros _. simpl. reflexivity.
           + intros [H1 H2]. simpl in H1, H2. lia.
           + intros [HnL HnU]. exfalso. apply HnL. split; simpl; lia.
        -- repeat split; [ intros _ | intros _ | intros [_ _] ];
           exfalso; simpl in Hlt; lia.
Qed.