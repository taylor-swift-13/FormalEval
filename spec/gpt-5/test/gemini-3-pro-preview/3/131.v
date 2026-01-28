Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_below_zero : below_zero_spec [1; 2; -3; 4; -5; 6; -7; 8; -9; -16; 10; -11; 12; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; -27; 29; -29; 30; -31; -31]%Z true.
Proof.
  set (l := [1; 2; -3; 4; -5; 6; -7; 8; -9; -16; 10; -11; 12; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; -27; 29; -29; 30; -31; -31]%Z).
  unfold below_zero_spec.
  split.
  - split; [intro | intro; reflexivity].
    exists [1; 2; -3; 4; -5]%Z.
    exists [6; -7; 8; -9; -16; 10; -11; 12; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; -27; 29; -29; 30; -31; -31]%Z.
    split.
    + unfold l. reflexivity.
    + unfold sum_list. simpl. lia.
  - split.
    + intro H. discriminate H.
    + intro H.
      assert (Heq: l = ([1; 2; -3; 4; -5] ++ [6; -7; 8; -9; -16; 10; -11; 12; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; -27; 29; -29; 30; -31; -31])%Z).
      { unfold l. reflexivity. }
      specialize (H [1; 2; -3; 4; -5]%Z [6; -7; 8; -9; -16; 10; -11; 12; -13; 14; -15; 16; -17; 18; -19; 20; -21; 22; -23; 24; -25; 26; -27; 29; -29; 30; -31; -31]%Z Heq).
      unfold sum_list in H. simpl in H. lia.
Qed.