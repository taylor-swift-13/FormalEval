Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_90_pre (l : list Z) : Prop := True.

Definition problem_90_spec (l : list Z) (res : option Z) : Prop :=
  match res with
  | Some z =>
    exists s1,
      In s1 l /\
      (forall x, In x l -> s1 <= x) /\
      In z l /\
      s1 < z /\
      (forall y, In y l -> s1 < y -> z <= y)
  | None =>
    ~ (exists x y, In x l /\ In y l /\ x <> y)
  end.

Example problem_90_test_case :
  problem_90_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z] (Some 2%Z).
Proof.
  unfold problem_90_spec; simpl.
  exists 1%Z.
  repeat split.
  - apply in_eq.
  - intros x Hx.
    apply in_inv in Hx.
    destruct Hx as [Hx | Hx]; [subst; lia|].
    apply in_inv in Hx.
    destruct Hx as [Hx | Hx]; [subst; lia|].
    apply in_inv in Hx.
    destruct Hx as [Hx | Hx]; [subst; lia|].
    apply in_inv in Hx.
    destruct Hx as [Hx | Hx]; [subst; lia|].
    apply in_inv in Hx.
    destruct Hx as [Hx | Hx]; [subst; lia|].
    apply in_nil in Hx; contradiction.
  - apply in_cons. apply in_eq.
  - lia.
  - intros y Hy Hlt.
    apply in_inv in Hy.
    destruct Hy as [Hy | Hy].
    + subst. lia.
    + apply in_inv in Hy.
      destruct Hy as [Hy | Hy].
      * subst. lia.
      * apply in_inv in Hy.
        destruct Hy as [Hy | Hy].
        { subst. lia. }
        { apply in_inv in Hy.
          destruct Hy as [Hy | Hy].
          { subst. lia. }
          { apply in_inv in Hy.
            destruct Hy as [Hy | Hy].
            { subst. lia. }
            { apply in_nil in Hy. contradiction. }
          }
        }
Qed.