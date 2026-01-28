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

Example test_zeros : below_zero_spec [0%Z; 0%Z; 0%Z; 0%Z; 0%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      (* We destruct prefix iteratively to check all possible prefixes of the list [0;0;0;0;0] *)
      destruct prefix as [|z0 prefix]; [unfold sum_list in Hsum; simpl in Hsum; lia|].
      simpl in Heq; injection Heq as Ez0 Heq; subst z0.
      destruct prefix as [|z1 prefix]; [unfold sum_list in Hsum; simpl in Hsum; lia|].
      simpl in Heq; injection Heq as Ez1 Heq; subst z1.
      destruct prefix as [|z2 prefix]; [unfold sum_list in Hsum; simpl in Hsum; lia|].
      simpl in Heq; injection Heq as Ez2 Heq; subst z2.
      destruct prefix as [|z3 prefix]; [unfold sum_list in Hsum; simpl in Hsum; lia|].
      simpl in Heq; injection Heq as Ez3 Heq; subst z3.
      destruct prefix as [|z4 prefix]; [unfold sum_list in Hsum; simpl in Hsum; lia|].
      simpl in Heq; injection Heq as Ez4 Heq; subst z4.
      destruct prefix as [|z5 prefix]; [unfold sum_list in Hsum; simpl in Hsum; lia|].
      (* If prefix has more elements than operations, it's impossible *)
      simpl in Heq; discriminate Heq.
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      (* Similarly, check all prefixes to show sum >= 0 *)
      destruct prefix as [|z0 prefix]; [unfold sum_list; simpl; lia|].
      simpl in Heq; injection Heq as Ez0 Heq; subst z0.
      destruct prefix as [|z1 prefix]; [unfold sum_list; simpl; lia|].
      simpl in Heq; injection Heq as Ez1 Heq; subst z1.
      destruct prefix as [|z2 prefix]; [unfold sum_list; simpl; lia|].
      simpl in Heq; injection Heq as Ez2 Heq; subst z2.
      destruct prefix as [|z3 prefix]; [unfold sum_list; simpl; lia|].
      simpl in Heq; injection Heq as Ez3 Heq; subst z3.
      destruct prefix as [|z4 prefix]; [unfold sum_list; simpl; lia|].
      simpl in Heq; injection Heq as Ez4 Heq; subst z4.
      destruct prefix as [|z5 prefix]; [unfold sum_list; simpl; lia|].
      simpl in Heq; discriminate Heq.
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.