Require Import String Ascii Arith Bool Lia List.

Open Scope string_scope.

Definition IsLow (c : ascii) : bool :=
  (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
  (nat_of_ascii c <=? nat_of_ascii "z")%nat.

Definition IsUp (c : ascii) : bool :=
  (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
  (nat_of_ascii c <=? nat_of_ascii "Z")%nat.

Definition Upper (c : ascii) : ascii :=
  if IsLow c then ascii_of_nat (nat_of_ascii c - 32) else c.

Definition Lower (c : ascii) : ascii :=
  if IsUp c then ascii_of_nat (nat_of_ascii c + 32) else c.

Fixpoint flip_case (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      let c' := if IsLow c then Upper c
                else if IsUp c then Lower c
                else c in
      String c' (flip_case s')
  end.

Definition problem_27_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  (forall (i : nat) (c : ascii),
    i < String.length input ->
    String.get i input = Some c ->
    (IsLow c = true -> String.get i output = Some (Upper c)) /\
    (IsUp c = true -> String.get i output = Some (Lower c)) /\
    (IsLow c = false /\ IsUp c = false -> String.get i output = Some c)).

Example flip_case_test_empty : problem_27_spec "" "".
Proof.
  unfold problem_27_spec.
  split.
  - reflexivity.
  - intros i c Hlen Hget.
    lia.
Qed.