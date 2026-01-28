Require Import String Ascii Arith Bool List.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(* Definitions provided in the specification, corrected for Coq syntax (char literals) *)

Definition IsLow (c : ascii) : Prop :=
  (nat_of_ascii "a"%char <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "z"%char)%nat.

Definition IsUp (c : ascii) : Prop :=
  (nat_of_ascii "A"%char <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "Z"%char)%nat.

Definition Upper (c : ascii) : ascii :=
  if (nat_of_ascii "a"%char <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "z"%char)%nat
  then ascii_of_nat (nat_of_ascii c - 32)
  else c.

Definition Lower (c : ascii) : ascii :=
  if (nat_of_ascii "A"%char <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "Z"%char)%nat
  then ascii_of_nat (nat_of_ascii c + 32)
  else c.

(* Pre-condition *)
Definition problem_27_pre (input : string) : Prop := True.

(* Specification *)
Definition problem_27_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  (forall (i : nat) (c : ascii),
    i < String.length input ->
    String.get i input = Some c ->
    (IsLow c -> String.get i output = Some (Upper c)) /\
    (IsUp c -> String.get i output = Some (Lower c)) /\
    (~IsLow c /\ ~IsUp c -> String.get i output = Some c)).

(* Test case proof *)
Example test_flip_case_numbers : problem_27_spec "1234" "1234".
Proof.
  unfold problem_27_spec.
  split.
  - reflexivity.
  - intros i c Hlen Hget.
    destruct i.
    + simpl in Hget. inversion Hget. subst.
      repeat split; intro H; try (compute in H; contradiction); reflexivity.
    + destruct i.
      * simpl in Hget. inversion Hget. subst.
        repeat split; intro H; try (compute in H; contradiction); reflexivity.
      * destruct i.
        -- simpl in Hget. inversion Hget. subst.
           repeat split; intro H; try (compute in H; contradiction); reflexivity.
        -- destruct i.
           ++ simpl in Hget. inversion Hget. subst.
              repeat split; intro H; try (compute in H; contradiction); reflexivity.
           ++ simpl in Hlen. inversion Hlen.
Qed.