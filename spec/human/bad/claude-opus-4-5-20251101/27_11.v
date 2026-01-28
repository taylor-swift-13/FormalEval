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

Example test_flip_case_digits : problem_27_spec "1234" "1234".
Proof.
  unfold problem_27_spec.
  split.
  - simpl. reflexivity.
  - intros i c Hi Hget.
    unfold IsLow, IsUp.
    simpl in Hi.
    destruct i as [|[|[|[|n]]]].
    + simpl in Hget. injection Hget as Hc. subst c.
      split; [intro H; simpl in H; lia|].
      split; [intro H; simpl in H; lia|].
      intro _. simpl. reflexivity.
    + simpl in Hget. injection Hget as Hc. subst c.
      split; [intro H; simpl in H; lia|].
      split; [intro H; simpl in H; lia|].
      intro _. simpl. reflexivity.
    + simpl in Hget. injection Hget as Hc. subst c.
      split; [intro H; simpl in H; lia|].
      split; [intro H; simpl in H; lia|].
      intro _. simpl. reflexivity.
    + simpl in Hget. injection Hget as Hc. subst c.
      split; [intro H; simpl in H; lia|].
      split; [intro H; simpl in H; lia|].
      intro _. simpl. reflexivity.
    + lia.
Qed.