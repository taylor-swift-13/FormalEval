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

Fixpoint flip_case (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
    let c' := if (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
                 (nat_of_ascii c <=? nat_of_ascii "z")%nat
              then ascii_of_nat (nat_of_ascii c - 32)
              else if (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
                       (nat_of_ascii c <=? nat_of_ascii "Z")%nat
                   then ascii_of_nat (nat_of_ascii c + 32)
                   else c
    in String c' (flip_case s')
  end.

Example test_flip_case_empty :
  problem_27_spec "" (flip_case "").
Proof.
  unfold problem_27_spec.
  split.
  - simpl. reflexivity.
  - intros i c Hlt Hget.
    simpl in Hget.
    discriminate Hget.
Qed.