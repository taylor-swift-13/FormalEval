Require Import Arith.
Require Import Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example_23_1 : problem_24_pre 23 /\ problem_24_spec 23 1.
Proof.
  split.
  - unfold problem_24_pre. lia.
  - unfold problem_24_spec.
    split.
    + simpl. reflexivity.
    + split.
      * lia.
      * intros i [Hi_pos Hi_lt] Hi_div.
        destruct i as [|i'].
        { lia. }
        destruct i' as [|i''].
        { lia. }
        destruct i'' as [|i3].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i3 as [|i4].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i4 as [|i5].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i5 as [|i6].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i6 as [|i7].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i7 as [|i8].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i8 as [|i9].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i9 as [|i10].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i10 as [|i11].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i11 as [|i12].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i12 as [|i13].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i13 as [|i14].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i14 as [|i15].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i15 as [|i16].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i16 as [|i17].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i17 as [|i18].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i18 as [|i19].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i19 as [|i20].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i20 as [|i21].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i21 as [|i22].
        { exfalso. simpl in Hi_div. discriminate. }
        destruct i22 as [|i23].
        { exfalso. simpl in Hi_div. discriminate. }
        { exfalso. lia. }
Qed.