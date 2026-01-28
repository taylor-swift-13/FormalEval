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

Example test_flip_case_violent : problem_27_spec "These violent delights have violent ends" "tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS".
Proof.
  unfold problem_27_spec.
  split.
  - simpl. reflexivity.
  - intros i c Hi Hget.
    split; [| split].
    + intro HLow.
      unfold IsLow in HLow.
      destruct HLow as [Hlo Hhi].
      unfold Upper.
      destruct i; simpl in Hget; inversion Hget; subst; simpl;
      try (compute in Hlo; lia);
      try reflexivity.
      destruct i; simpl in Hget; inversion Hget; subst; simpl;
      try reflexivity.
      destruct i; simpl in Hget; inversion Hget; subst; simpl;
      try reflexivity.
      destruct i; simpl in Hget; inversion Hget; subst; simpl;
      try reflexivity.
      destruct i; simpl in Hget; inversion Hget; subst; simpl;
      try reflexivity.
      destruct i; simpl in Hget; inversion Hget; subst; simpl;
      try (compute in Hlo; lia);
      try reflexivity.
      do 35 (destruct i; [simpl in Hget; inversion Hget; subst; simpl; try reflexivity; try (compute in Hlo; lia) |]).
      simpl in Hi. lia.
    + intro HUp.
      unfold IsUp in HUp.
      destruct HUp as [Hlo Hhi].
      unfold Lower.
      destruct i; simpl in Hget; inversion Hget; subst; simpl;
      try reflexivity;
      try (compute in Hlo; lia);
      try (compute in Hhi; lia).
      do 40 (destruct i; [simpl in Hget; inversion Hget; subst; simpl; try reflexivity; try (compute in Hlo; lia); try (compute in Hhi; lia) |]).
      simpl in Hi. lia.
    + intros [HnotLow HnotUp].
      destruct i; simpl in Hget; inversion Hget; subst; simpl.
      * exfalso. apply HnotUp. unfold IsUp. compute. lia.
      * do 40 (destruct i; [simpl in Hget; inversion Hget; subst; simpl;
        try reflexivity;
        try (exfalso; apply HnotLow; unfold IsLow; compute; lia);
        try (exfalso; apply HnotUp; unfold IsUp; compute; lia) |]).
        simpl in Hi. lia.
Qed.