Require Import String Ascii Arith Bool.

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

Definition Spec (input output : string) : Prop :=
  String.length input = String.length output /\
  (forall (i : nat) (c : ascii),
    i < String.length input ->
    String.get i input = Some c ->
    (IsLow c -> String.get i output = Some (Upper c)) /\
    (IsUp c -> String.get i output = Some (Lower c)) /\
    (~IsLow c /\ ~IsUp c -> String.get i output = Some c)).

Example flip_case_test :
  Spec "PythoPtoGGlE Meython I su Funn Iss Fun" "pYTHOpTOggLe mEYTHON i SU fUNN iSS fUN".
Proof.
  unfold Spec.
  split.
  - reflexivity.
  - intros i c Hi Hget.
    destruct i as [|i]; simpl in *.
    + destruct (String.get 0 "PythoPtoGGlE Meython I su Funn Iss Fun") eqn:Hget0.
      * assert (String.get 0 "pYTHOpTOggLe mEYTHON i SU fUNN iSS fUN" = Some (Lower a)).