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

Example test_below_zero : below_zero_spec [0%Z; 35%Z; 1%Z; 36%Z; 36%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|p0 prefix].
      * (* prefix = [] *)
        unfold sum_list in Hsum. simpl in Hsum. lia.
      * destruct prefix as [|p1 prefix].
        { injection Heq as H0 _. subst. unfold sum_list in Hsum. simpl in Hsum. lia. }
        destruct prefix as [|p2 prefix].
        { injection Heq as H0 H1 _. subst. unfold sum_list in Hsum. simpl in Hsum. lia. }
        destruct prefix as [|p3 prefix].
        { injection Heq as H0 H1 H2 _. subst. unfold sum_list in Hsum. simpl in Hsum. lia. }
        destruct prefix as [|p4 prefix].
        { injection Heq as H0 H1 H2 H3 _. subst. unfold sum_list in Hsum. simpl in Hsum. lia. }
        destruct prefix as [|p5 prefix].
        { injection Heq as H0 H1 H2 H3 H4 _. subst. unfold sum_list in Hsum. simpl in Hsum. lia. }
        (* Overflow *)
        simpl in Heq. injection Heq as _ _ _ _ _ Hcontra. discriminate Hcontra.
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      destruct prefix as [|p0 prefix].
      * (* prefix = [] *)
        unfold sum_list. simpl. lia.
      * destruct prefix as [|p1 prefix].
        { injection Heq as H0 _. subst. unfold sum_list. simpl. lia. }
        destruct prefix as [|p2 prefix].
        { injection Heq as H0 H1 _. subst. unfold sum_list. simpl. lia. }
        destruct prefix as [|p3 prefix].
        { injection Heq as H0 H1 H2 _. subst. unfold sum_list. simpl. lia. }
        destruct prefix as [|p4 prefix].
        { injection Heq as H0 H1 H2 H3 _. subst. unfold sum_list. simpl. lia. }
        destruct prefix as [|p5 prefix].
        { injection Heq as H0 H1 H2 H3 H4 _. subst. unfold sum_list. simpl. lia. }
        (* Overflow *)
        simpl in Heq. injection Heq as _ _ _ _ _ Hcontra. discriminate Hcontra.
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.