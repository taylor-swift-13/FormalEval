Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_even (n : Z) : Prop := Z.even n = true.

Definition is_odd (n : Z) : Prop := Z.odd n = true.

Definition all_odd (arr : list Z) : Prop :=
  forall x, In x arr -> is_odd x.

Definition has_even (arr : list Z) : Prop :=
  exists x, In x arr /\ is_even x.

Definition is_smallest_even (arr : list Z) (v : Z) : Prop :=
  In v arr /\
  is_even v /\
  forall x, In x arr -> is_even x -> v <= x.

Definition is_first_index_of (arr : list Z) (v : Z) (idx : nat) : Prop :=
  (idx < length arr)%nat /\
  nth idx arr 0 = v /\
  forall j, (j < idx)%nat -> nth j arr 0 <> v.

Definition pluck_spec (arr : list Z) (result : list Z) : Prop :=
  (arr = [] -> result = []) /\
  (arr <> [] -> all_odd arr -> result = []) /\
  (arr <> [] -> has_even arr ->
    exists min_even idx,
      is_smallest_even arr min_even /\
      is_first_index_of arr min_even idx /\
      result = [min_even; Z.of_nat idx]).

Example test_pluck : pluck_spec [4; 2; 3] [2; 1].
Proof.
  unfold pluck_spec.
  split.
  - (* Case: arr = [] *)
    intro H.
    discriminate H.
  - split.
    + (* Case: arr <> [] -> all_odd arr -> result = [] *)
      intros _ Hodd.
      assert (In 4 [4; 2; 3]) as Hin. { simpl. left. reflexivity. }
      specialize (Hodd 4 Hin).
      unfold is_odd in Hodd.
      simpl in Hodd.
      discriminate Hodd.
    + (* Case: arr <> [] -> has_even arr -> result = [min_even; index] *)
      intros _ _.
      exists 2, 1%nat.
      split.
      * (* is_smallest_even *)
        unfold is_smallest_even.
        split.
        -- (* In 2 arr *)
           simpl. right. left. reflexivity.
        -- split.
           ++ (* is_even 2 *)
              unfold is_even. reflexivity.
           ++ (* forall x, In x arr -> is_even x -> 2 <= x *)
              intros x Hin Hex.
              simpl in Hin.
              destruct Hin as [H4 | [H2 | [H3 | Hnil]]].
              ** (* x = 4 *)
                 rewrite H4. lia.
              ** (* x = 2 *)
                 rewrite H2. lia.
              ** (* x = 3 *)
                 rewrite H3 in Hex.
                 unfold is_even in Hex.
                 simpl in Hex.
                 discriminate Hex.
              ** (* False *)
                 contradiction.
      * split.
        -- (* is_first_index_of *)
           unfold is_first_index_of.
           split.
           ++ (* idx < length *)
              simpl. lia.
           ++ split.
              ** (* nth idx ... = v *)
                 simpl. reflexivity.
              ** (* forall j < idx ... *)
                 intros j Hj.
                 assert (j = 0%nat) as Hzero by lia.
                 subst j.
                 simpl.
                 lia.
        -- (* result equality *)
           simpl. reflexivity.
Qed.