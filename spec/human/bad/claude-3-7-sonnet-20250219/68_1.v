Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition problem_68_pre (arr : list nat) : Prop := True.

Definition problem_68_spec (arr : list nat) (output : option (nat * nat)) : Prop :=
  match output with
  | None =>
      forall val, In val arr -> Nat.even val = false
  | Some (v, i) =>
      i < length arr /\
      nth i arr 1 = v /\
      Nat.even v = true /\
      (forall val, In val arr -> Nat.even val = true -> v <= val) /\
      (forall j, j < i -> nth j arr 1 <> v)
  end.

Example test_pluck_1 :
  problem_68_spec [4;2;3] (Some (2,1)).
Proof.
  unfold problem_68_spec.
  repeat split.
  - (* i < length arr *)
    simpl. lia.
  - (* nth i arr 1 = v *)
    simpl. reflexivity.
  - (* Nat.even v = true *)
    simpl. reflexivity.
  - (* v <= all even vals *)
    intros val HIn HEven.
    simpl in HIn.
    destruct HIn as [H4 | [H2 | H3]]; subst val.
    + (* val = 4 *)
      assert (Nat.even 4 = true) by reflexivity.
      rewrite <- H in HEven. lia.
    + (* val = 2 *)
      assert (Nat.even 2 = true) by reflexivity.
      rewrite <- H in HEven. lia.
    + (* val = 3 *)
      (* 3 is not even, contradiction *)
      rewrite H3 in HEven.
      simpl in HEven.
      destruct (Nat.even 3) eqn:E; discriminate.
  - (* minimal index for v *)
    intros j Hlt.
    simpl.
    destruct j.
    + (* j = 0 *)
      simpl. discriminate.
    + (* j >= 1 *)
      destruct j; [simpl; discriminate|].
      lia.
Qed.